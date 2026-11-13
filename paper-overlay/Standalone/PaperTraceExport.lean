/-
  PaperTraceExport: replay Nazrin atomization on a list of theorems and emit
  goal-aware ExprGraph traces plus a first-version NPA-oriented JSONL view.

  Usage:
    lean --run Standalone/PaperTraceExport.lean \
      MODULE THEOREM_LIST_TSV OUTPUT_DIR [LIMIT]

  Outputs (one JSON object per line, UTF-8):
    steps.jsonl    one row per atomization step, with its goal graph
    graphs.jsonl   goal_id -> goal graph, including every child goal
    failures.jsonl per-theorem failures (export continues)
    meta.json      counts, timing, toolchain, input hash, warning count

  This file intentionally duplicates the atomization loop instead of changing
  `Standalone/AtomizerCore.lean`; the replay order and goal scheduling match
  `integratedAtomize` exactly.
-/
import Standalone.AtomizerCore
import Standalone.GoalGraphCore
import Lean.Data.Json

open Lean Nazrin

namespace PaperTraceExport

/-! ## Tactic -> JSON parameter mapping -/

/-- Render an expression for the `expression` escape hatch. -/
def ppExprString (e : Expr) : MetaM String := do
  let message ← Meta.ppExpr e
  return message.pretty

/-- Head constant of an application, if any.  We never invent a pointer label
for a non-constant expression. -/
def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const name _ => some name
  | _ => none

structure TacticJson where
  json : Json
  unmodeled : Bool

/-- Map an `AtomicTactic` to the NPA parameter schema.  Parameters that cannot
be recovered from the tactic payload are omitted, never guessed.  When an
expression payload is not a constant or a local variable we keep its pretty
printed form under `expression` and set `unmodeled: true`. -/
def tacticToJson (fvarNames : Std.HashMap FVarId String) (tactic : AtomicTactic) : MetaM TacticJson := do
  let fvarName (id : FVarId) : String :=
    fvarNames[id]?.getD id.name.toString
  let nameMode (name : Name) : String :=
    if name.isAnonymous then "anonymous" else "explicit"
  let mut params : Array (String × Json) := #[]
  let mut unmodeled := false
  let mut expression? : Option String := none
  match tactic with
  | .intro name =>
    params := params.push ("name_mode", toJson (nameMode name))
  | .pi name =>
    params := params.push ("name_mode", toJson (nameMode name))
  | .revert fvarId =>
    params := params.push ("free_variable", toJson (fvarName fvarId))
  | .apply e | .motivatedApply e | .exact e =>
    match headConst? e with
    | some name => params := params.push ("premise", toJson name.toString)
    | none =>
      expression? := some (← ppExprString e)
      unmodeled := true
  | .generalize name e =>
    params := params.push ("name_mode", toJson (nameMode name))
    match e with
    | .fvar id => params := params.push ("free_variable", toJson (fvarName id))
    | _ =>
      expression? := some (← ppExprString e)
      unmodeled := true
  | .cases major =>
    params := params.push ("cases_mode", toJson "constructors")
    match major with
    | .fvar id => params := params.push ("free_variable", toJson (fvarName id))
    | _ =>
      expression? := some (← ppExprString major)
      unmodeled := true
  | .induction major recursor =>
    params := params.push ("induction_mode",
      toJson (if recursor.isAnonymous then "ordinary" else "using"))
    if !recursor.isAnonymous then
      params := params.push ("premise", toJson recursor.toString)
    match major with
    | .fvar id => params := params.push ("free_variable", toJson (fvarName id))
    | _ =>
      expression? := some (← ppExprString major)
      unmodeled := true
  | .rewrite _fvarId? pos heq0 symm allOccs =>
    params := params.push ("direction", toJson (if symm then "backward" else "forward"))
    params := params.push ("occurrence", toJson (if allOccs then "all" else "first"))
    params := params.push ("locus", toJson (GoalGraphCore.posToPath pos))
    match headConst? heq0 with
    | some name => params := params.push ("premise", toJson name.toString)
    | none =>
      expression? := some (← ppExprString heq0)
      unmodeled := true
  | .generalizeAt _binderName pos =>
    params := params.push ("locus", toJson (GoalGraphCore.posToPath pos))
  | .unfold fvarId? name =>
    params := params.push ("premise", toJson name.toString)
    params := params.push ("target_mode", toJson (if fvarId?.isSome then "hypotheses" else "goal"))
  | .normalize =>
    params := params.push ("target_mode", toJson "goal")
  | .reduceBeta =>
    params := params.push ("target_mode", toJson "goal")
  | .contradiction | .assumption | .decide | .refl | .inhabit | .tailArg => pure ()
  | .define _name value =>
    expression? := some (← ppExprString value)
    unmodeled := true
  | .have _name type =>
    expression? := some (← ppExprString type)
    unmodeled := true
  | .let _name value =>
    expression? := some (← ppExprString value)
    unmodeled := true
  | .raw text =>
    params := params.push ("text", toJson text)
    unmodeled := true
  let extra : List (String × Json) :=
    (if unmodeled then [("unmodeled", toJson true)] else []) ++
    match expression? with
    | some text => [("expression", toJson text)]
    | none => []
  let kindName := match tactic with
    | .raw _ => "raw"
    | _ => AtomicTactic.kind tactic
  return {
    json := Json.mkObj <|
      [("kind", toJson kindName),
       ("parameters", Json.mkObj params.toList)] ++ extra
    unmodeled := unmodeled
  }

/-! ## Trace records -/

structure TraceStep where
  thmName : String
  stepIndex : Nat
  goalId : String
  goalGraph : Json
  tactic : Json
  children : Array String

structure TheoremTrace where
  steps : Array TraceStep
  graphs : Array (String × Json)
  warnings : Array String
  unmodeledSteps : Nat := 0

def traceStepToJson (step : TraceStep) : Json :=
  Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("theorem", toJson step.thmName),
    ("step", toJson step.stepIndex),
    ("goal_id", toJson step.goalId),
    ("goal_graph", step.goalGraph),
    ("tactic", step.tactic),
    ("children", Json.arr (step.children.map toJson))]

def graphRecordToJson (thmName : String) (goalId : String) (graph : Json) : Json :=
  Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("theorem", toJson thmName),
    ("goal_id", toJson goalId),
    ("graph", graph)]

/-- Assign a deterministic, theorem-local goal id on first sight. -/
def ensureGoalId (pre : String) (ids : Array (MVarId × String)) (next : Nat)
    (goal : MVarId) : String × Nat × Array (MVarId × String) :=
  match ids.find? fun entry => entry.1 == goal with
  | some entry => (entry.2, next, ids)
  | none =>
    let id := s!"{pre}:g{next}"
    (id, next + 1, ids.push (goal, id))

def hasGraph (graphs : Array (String × Json)) (goalId : String) : Bool :=
  graphs.any fun entry => entry.1 == goalId

/-- Replay atomization for one theorem.  This mirrors `integratedAtomize`:
same goal ordering (descending successor count), same progress rule, and the
same resume call.  The only additions are graph capture and trace records. -/
def atomizationTrace (thmName : Name) (info : ConstantInfo) : MetaM TheoremTrace := do
  let some value := info.value? | throwError "theorem has no proof value"
  let root := (← Meta.mkFreshExprSyntheticOpaqueMVar info.type).mvarId!
  let initialState ← Pantograph.GoalState.createFromMVars [root] root
  let atomizeM : Nazrin.Atomization.AtomizeT MetaM TheoremTrace := do
    let mut state := initialState
    let mut steps : Array TraceStep := #[]
    let mut graphs : Array (String × Json) := #[]
    let mut warnings : Array String := #[]
    let mut unmodeledSteps := 0
    let mut goalIds : Array (MVarId × String) := #[]
    let mut nextGoal := 0
    let mut stepIndex := 0
    let pre := thmName.toString
    let (rootId, nextGoal0, goalIds0) := ensureGoalId pre goalIds nextGoal root
    nextGoal := nextGoal0
    goalIds := goalIds0
    let (rootGraph, rootWarnings) ← state.withContext root (GoalGraphCore.buildGoalGraphAsFull root rootId)
    graphs := graphs.push (rootId, rootGraph)
    warnings := warnings ++ rootWarnings
    for _ in Array.range 1000 do
      if state.goals.isEmpty then
        break
      let solutionMap := (← get).solutionMap
      let goals := state.goalsArray.qsort fun g1 g2 =>
        let n1 := (solutionMap.get? g1).map fun { successors, .. } => successors.size
        let n2 := (solutionMap.get? g2).map fun { successors, .. } => successors.size
        n1.get! > n2.get!
      let mut progressed := false
      for goal in goals do
        state.restoreMetaM
        let fvarNames := GoalGraphCore.localDisplayNames (← goal.getDecl).lctx
        match ← Nazrin.Atomization.step' state goal with
        | .defer => continue
        | .failure message => throwError "Atomization failed: {message}"
        | .next tactic nextState =>
          let (goalId, ng, ids) := ensureGoalId pre goalIds nextGoal goal
          nextGoal := ng
          goalIds := ids
          if !hasGraph graphs goalId then
            let (graph, graphWarnings) ← try
              state.withContext goal (GoalGraphCore.buildGoalGraphAsFull goal goalId)
            catch ex =>
              throwError "graph build failed for {goalId} ({goal.name}): {← ex.toMessageData.toString}"
            graphs := graphs.push (goalId, graph)
            warnings := warnings ++ graphWarnings
          let mut childIds : Array String := #[]
          for child in nextState.goals do
            let (childId, ng2, ids2) := ensureGoalId pre goalIds nextGoal child
            nextGoal := ng2
            goalIds := ids2
            if !hasGraph graphs childId then
              let (childGraph, childWarnings) ← try
                nextState.withContext child (GoalGraphCore.buildGoalGraphAsFull child childId)
              catch ex =>
                throwError "child graph build failed for {childId} ({child.name}): {← ex.toMessageData.toString}"
              graphs := graphs.push (childId, childGraph)
              warnings := warnings ++ childWarnings
            childIds := childIds.push childId
          let tacticJson ← tacticToJson fvarNames tactic
          if tacticJson.unmodeled then
            unmodeledSteps := unmodeledSteps + 1
          let goalGraph := match graphs.find? (fun entry => entry.1 == goalId) with
            | some entry => entry.2
            | none => Json.mkObj []
          steps := steps.push {
            thmName := pre
            stepIndex := stepIndex
            goalId := goalId
            goalGraph := goalGraph
            tactic := tacticJson.json
            children := childIds
          }
          stepIndex := stepIndex + 1
          let .ok resumed := nextState.resume
              (nextState.goals ++ goals.toList.filter (· ≠ goal))
            | throwError "Could not resume atomization state"
          state := resumed
          progressed := true
          break
      if !progressed then
        throwError s!"Goal exhaustion. No goals ({state.goals.length}) in the active set can make progress"
    unless state.goals.isEmpty do
      throwError s!"{state.goals.length} goals left after iteration limit"
    return { steps := steps, graphs := graphs, warnings := warnings, unmodeledSteps := unmodeledSteps }
  let rootState ← Nazrin.Atomization.createRootState root value
  atomizeM.run' rootState

/-! ## CLI -/

def usage : IO Unit := do
  IO.eprintln "Usage: lean --run Standalone/PaperTraceExport.lean MODULE THEOREM_LIST_TSV OUTPUT_DIR [LIMIT]"
  IO.eprintln "  THEOREM_LIST_TSV needs a 'theorem' column (header) or one theorem per line."
  IO.eprintln "  LIMIT bounds the number of theorem rows processed."
  IO.eprintln "  NAZRIN_TRACE_MAX_HEARTBEATS overrides the heartbeat limit (default 200000)."

/-- Default heartbeat budget, matching Lean's own default. -/
def defaultMaxHeartbeats : Nat := 200000

/-- Parse a positive decimal integer.  Reject signs, whitespace, underscores and
zero so a malformed environment variable cannot silently disable the limit. -/
def parseMaxHeartbeats (raw : String) : Except String Nat :=
  if raw.isEmpty || !raw.all Char.isDigit then
    .error s!"expected a positive integer, got {repr raw}"
  else
    match raw.toNat? with
    | some 0 => .error s!"expected a positive integer, got {repr raw}"
    | some value => .ok value
    | none => .error s!"expected a positive integer, got {repr raw}"

/-- Read `NAZRIN_TRACE_MAX_HEARTBEATS`, defaulting to `defaultMaxHeartbeats`.
Reports an invalid value and returns `none`, so `main` can exit non-zero. -/
def maxHeartbeatsFromEnv : IO (Option Nat) := do
  match ← IO.getEnv "NAZRIN_TRACE_MAX_HEARTBEATS" with
  | none => pure (some defaultMaxHeartbeats)
  | some raw =>
    match parseMaxHeartbeats raw with
    | .ok value => pure (some value)
    | .error message =>
      IO.eprintln s!"error: invalid NAZRIN_TRACE_MAX_HEARTBEATS: {message}"
      pure none

def parseTheoremList (path : System.FilePath) (limit? : Option Nat) : IO (Array Name) := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").map (fun line => line.trimAscii.toString) |>.filter (fun line => !line.isEmpty)
  let lines := lines.toArray
  if lines.isEmpty then
    throw <| IO.userError s!"{path}: empty theorem list"
  let header := (lines[0]!).splitOn "\t" |>.map (fun cell => cell.trimAscii.toString)
  let (column, start) ←
    match header.findIdx? (· == "theorem") with
    | some index => pure (index, 1)
    | none =>
      if lines.all fun line => (line.splitOn "\t").length == 1 then
        pure (0, 0)
      else
        throw <| IO.userError s!"{path}: missing 'theorem' column in header"
  let mut names : Array Name := #[]
  let mut seen : Std.HashSet String := {}
  for line in lines.drop start do
    let cells := line.splitOn "\t"
    if column >= cells.length then
      throw <| IO.userError s!"{path}: row has no column {column}: {line}"
    let name := (cells[column]!).trimAscii.toString
    unless name.isEmpty do
      unless seen.contains name do
        names := names.push name.toName
        seen := seen.insert name
  let bounded := match limit? with
    | some limit => names.take limit
    | none => names
  if bounded.isEmpty then
    throw <| IO.userError s!"{path}: no theorem rows"
  return bounded

def sha256File (path : System.FilePath) : IO String := do
  try
    let output ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
    if output.exitCode == 0 then
      match output.stdout.splitOn " " with
      | hash :: _ => return hash.trimAscii.toString
      | [] => return "unavailable"
    else
      return "unavailable"
  catch _ =>
    return "unavailable"

def toolchainString : IO String := do
  if ← System.FilePath.pathExists "lean-toolchain" then
    return (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  else
    return Lean.versionString

structure Failure where
  thmName : String
  stage : String
  message : String

def failureToJson (failure : Failure) : Json :=
  Json.mkObj [
    ("theorem", toJson failure.thmName),
    ("stage", toJson failure.stage),
    ("message", toJson failure.message)]

def writeJsonLines (path : System.FilePath) (values : Array Json) : IO Unit := do
  IO.FS.withFile path .write fun handle => do
    for value in values do
      handle.putStrLn value.compress

def main (args : List String) : IO UInt32 := do
  let (moduleName, theoremList, outputDir, limit?) ← match args with
    | moduleName :: theoremList :: outputDir :: rest =>
      let limit? ← match rest with
        | [] => pure none
        | [limit] =>
          match limit.toNat? with
          | some limit => pure (some limit)
          | none => IO.eprintln s!"error: invalid LIMIT {limit}"; return 1
        | _ => usage; return 1
      pure (moduleName, theoremList, outputDir, limit?)
    | _ => usage; return 1
  let some maxHeartbeats ← maxHeartbeatsFromEnv
    | return 1
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Pantograph.initSearch ""
  let started ← IO.monoMsNow
  let names ← parseTheoremList theoremList limit?
  let env ← Lean.importModules #[{ module := moduleName.toName }] {} 1 (loadExts := true)
  IO.FS.createDirAll outputDir
  let outputPath : System.FilePath := outputDir
  -- Pass the option explicitly: the `-D` CLI flag does not reach this context.
  let coreContext ← Pantograph.createCoreContext #[s!"maxHeartbeats={maxHeartbeats}"]
  let mut steps : Array Json := #[]
  let mut graphs : Array Json := #[]
  let mut failures : Array Failure := #[]
  let mut warnings : Nat := 0
  let mut unmodeledSteps : Nat := 0
  let mut succeeded : Nat := 0
  let mut stepCount : Nat := 0
  for name in names do
    let thmName := name.toString
    let some info := env.find? name
      | failures := failures.push { thmName, stage := "lookup", message := "unknown constant" }
        continue
    unless info matches .thmInfo .. do
      failures := failures.push { thmName, stage := "not_theorem", message := "constant is not a theorem" }
      continue
    try
      match ← (Lean.Meta.MetaM.run' (atomizationTrace name info)).run coreContext
          { env := env } |>.toBaseIO with
      | .ok (trace, _) =>
        succeeded := succeeded + 1
        stepCount := stepCount + trace.steps.size
        warnings := warnings + trace.warnings.size
        unmodeledSteps := unmodeledSteps + trace.unmodeledSteps
        for step in trace.steps do
          steps := steps.push (traceStepToJson step)
        for (goalId, graph) in trace.graphs do
          graphs := graphs.push (graphRecordToJson thmName goalId graph)
      | .error exception =>
        failures := failures.push {
          thmName, stage := "atomization",
          message := ← exception.toMessageData.toString }
    catch exception =>
      failures := failures.push {
        thmName, stage := "internal",
        message := toString exception }
  writeJsonLines (outputPath / "steps.jsonl") steps
  writeJsonLines (outputPath / "graphs.jsonl") graphs
  writeJsonLines (outputPath / "failures.jsonl") (failures.map failureToJson)
  let nowMs ← IO.monoMsNow
  let elapsed := nowMs - started
  let inputSha ← sha256File theoremList
  let toolchain ← toolchainString
  let metaJson := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson moduleName),
    ("max_heartbeats", toJson maxHeartbeats),
    ("input", toJson theoremList),
    ("input_sha256", toJson inputSha),
    ("output_dir", toJson outputDir),
    ("toolchain", toJson toolchain),
    ("theorems_requested", toJson names.size),
    ("theorems_succeeded", toJson succeeded),
    ("theorems_failed", toJson failures.size),
    ("steps", toJson stepCount),
    ("graphs", toJson graphs.size),
    ("warnings", toJson warnings),
    ("unmodeled_steps", toJson unmodeledSteps),
    ("elapsed_ms", toJson elapsed),
    ("limit", toJson (limit?.map (fun n => toJson n) |>.getD Json.null))]
  IO.FS.writeFile (outputPath / "meta.json") (metaJson.pretty ++ "\n")
  IO.println s!"PaperTraceExport: {succeeded}/{names.size} theorem(s), {stepCount} step(s)"
  IO.println s!"  steps={outputPath / "steps.jsonl"}"
  IO.println s!"  failures={failures.size} warnings={warnings} elapsed_ms={elapsed}"
  return if succeeded == 0 then 1 else 0

end PaperTraceExport

def main (args : List String) : IO UInt32 :=
  PaperTraceExport.main args
