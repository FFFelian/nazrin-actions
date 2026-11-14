/-
  NPARepl: a small, line-oriented REPL for paper-aligned NPA proof search.

  This is deliberately independent of the unfinished NPA model.  It exposes
  Pantograph's string-tactic API over JSON so a Python driver can maintain a
  real Lean proof state without embedding NPA-specific parameters.

  Protocol (one JSON object per line):
    request  {"cmd":"start","theorem":"Nat.le_of_succ_le"}
    request  {"cmd":"apply","goal":0,"tactic":"intro h"}
    request  {"cmd":"goals"}
    request  {"cmd":"close"}
    response NAZRIN_NPA {"status":"ok", ...}

  Every proof-state response carries, per goal, both the v1 single-goal `graph`
  and the schema-2 whole-state `graph_v2` (with `graph_v2_goal_id` /
  `graph_v2_root` and a top-level `current_goal_roots` mapping).  See
  `experiments/exprgraph/v2/schema-v2.md`.

  Every response is emitted as exactly one line, prefixed with `NAZRIN_NPA `.
-/
import Pantograph.Library
import Standalone.GoalGraphCore
import Standalone.ExprGraphV2

open Lean
open Pantograph

namespace Nazrin.NPARepl

private def protocolPrefix : String := "NAZRIN_NPA "

/-- Error messages are bounded so a pathological tactic cannot flood the pipe. -/
private def maxMessageLength : Nat := 16384

private def truncate (message : String) : String :=
  (message.take maxMessageLength).toString

/-- Runtime configuration for all requests. -/
structure Runtime where
  env : Environment
  coreContext : Core.Context

/-- A saved proof branch.  `GoalState` is a persistent value, so keeping the
    state and our own goal list is enough to restore a branch exactly. -/
structure Snapshot where
  state : GoalState
  goals : List MVarId

/-- The live proof state.  `goals` is our own list of unresolved goal mvars;
    Pantograph's `GoalState.goals` only contains the goals active in the last
    focused tactic step. -/
structure Session where
  state : GoalState
  goals : List MVarId
  theoremName : String
  snapshots : Std.HashMap String Snapshot := {}

structure LoopResult where
  session : Option Session
  stop : Bool

private def reply (json : Json) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn (protocolPrefix ++ json.compress)
  stdout.flush

private def errorJson (kind message : String) : Json :=
  Json.mkObj [
    ("status", toJson "error"),
    ("kind", toJson kind),
    ("message", toJson (truncate message))]

private def okJson (fields : List (String × Json)) : Json :=
  Json.mkObj (("status", toJson "ok") :: fields)

private def exceptionMessage (exception : Exception) : IO String := do
  try
    return truncate (← exception.toMessageData.toString)
  catch _ =>
    return "internal exception (message formatting failed)"

private def renderMessages (messages : Array Message) : IO (Array String) := do
  messages.mapM fun message => do
    try
      return truncate (← message.toString)
    catch _ =>
      return "<unrenderable message>"

/-- Run a `TermElabM` action against the imported environment. -/
private def runTermElabM (runtime : Runtime) (m : Elab.TermElabM α) :
    IO (Except Exception α) := do
  let coreM := (m.run' (ctx := defaultElabContext)).run'
  match ← (coreM.run runtime.coreContext { env := runtime.env }).toBaseIO with
  | .ok (result, _) => return .ok result
  | .error exception => return .error exception

/-- Run a `MetaM` action against the imported environment. -/
private def runMetaM (runtime : Runtime) (m : MetaM α) :
    IO (Except Exception α) := do
  let coreM := m.run'
  match ← (coreM.run runtime.coreContext { env := runtime.env }).toBaseIO with
  | .ok (result, _) => return .ok result
  | .error exception => return .error exception

private def isAssigned (state : GoalState) (goal : MVarId) : Bool :=
  state.mctx.eAssignment.contains goal || state.mctx.dAssignment.contains goal

/-- Merge two goal lists while preserving order and removing duplicates. -/
private def mergeGoals (first second : List MVarId) : List MVarId :=
  second.foldl (init := first) fun acc goal =>
    if acc.contains goal then acc else acc ++ [goal]

/-- An array field extracted without throwing. -/
private def jsonArrayD (json : Json) (key : String) : Array Json :=
  match json.getObjValD key with
  | .arr values => values
  | _ => #[]

/-- The `(goal_id, root)` pair of one goal in a schema-2 proof-state graph.

The builder (`ExprGraphV2.buildGoalStateGraph`) emits one `goals[]` entry per
input mvar, in input order, so the graph index is the response goal index. -/
private def v2GoalRef? (graphV2 : Json) (index : Nat) : Option (String × Nat) := do
  let some entry := (jsonArrayD graphV2 "goals")[index]? | none
  let goalId := ExprGraphV2.jsonStrD entry "goal_id"
  if goalId.isEmpty then none
  let root ← (entry.getObjValD "root").getNat?.toOption
  return (goalId, root)

/-- The explicit `response id <-> schema-2 goal_id/root` mapping emitted next to
    `graph_v2`.  A client that cannot rely on array order can use this table. -/
private def currentGoalRootsJson (session : Session) (graphV2 : Json) : Array Json :=
  Id.run do
    let mut roots := #[]
    for index in [:session.goals.length] do
      let mvar := match session.goals[index]? with
        | some goal => goal.name.toString
        | none => ""
      let (goalId, root) := match v2GoalRef? graphV2 index with
        | some (goalId, root) => (toJson goalId, toJson root)
        | none => (Json.null, Json.null)
      roots := roots.push <| Json.mkObj [
        ("id", toJson index),
        ("mvar", toJson mvar),
        ("goal_id", goalId),
        ("root", root)]
    return roots

private def goalJson (index : Nat) (goal : Protocol.Goal) (graph : Json)
    (graphError : Option String) (graphV2 : Json) (graphV2Error : Option String) : Json :=
  let target := goal.target.pp?.getD "<unprintable target>"
  let vars := goal.vars.map fun decl =>
    let type := decl.type?.bind (·.pp?) |>.getD "<unprintable type>"
    Json.mkObj [
      ("name", toJson decl.userName.toString),
      ("internal", toJson decl.name.toString),
      ("type", toJson type)]
  let graphFields := match graphError with
    | some message => [("graph", graph), ("graph_error", toJson message)]
    | none => [("graph", graph)]
  let graphV2Fields := match graphV2Error with
    | some message => [("graph_v2", graphV2), ("graph_v2_error", toJson message)]
    | none =>
      match v2GoalRef? graphV2 index with
      | some (goalId, root) =>
        [("graph_v2", graphV2),
         ("graph_v2_goal_id", toJson goalId),
         ("graph_v2_root", toJson root)]
      | none => [("graph_v2", graphV2)]
  Json.mkObj <|
    [("id", toJson index),
     ("mvar", toJson goal.name.toString),
     ("userName", match goal.userName? with
       | some name => toJson name.toString
       | none => Json.null),
     ("target", toJson target),
     ("vars", toJson vars)] ++ graphFields ++ graphV2Fields

/-- Build the goal-aware ExprGraph for one live metavariable.  A graph failure
    is reported as `graph:null` plus `graph_error`; it must never abort the
    REPL, because a tactic may still be searchable without graph features. -/
private def goalGraph (runtime : Runtime) (state : GoalState) (goal : MVarId) :
    IO (Json × Option String) := do
  -- `buildGoalGraph` must see the metavariable context captured in `state`;
  -- the bare `runMetaM` context does not know the proof's fresh mvars.
  let coreM := (state.withContext' goal (GoalGraphCore.buildGoalGraph goal)).run'
  match ← (coreM.run runtime.coreContext { env := runtime.env }).toBaseIO with
  | .ok (graph, _) => return (graph, none)
  | .error exception =>
    let message ← exceptionMessage exception
    return (Json.null, some s!"goal graph failed: {message}")

/-- Build the schema-2 (coupled-goal) graph of the whole proof state.

The metavariable context is taken from `state`; `buildGoalStateGraph` needs it
to see the proof's fresh mvars.  We enter the local context of the first
tracked goal: every goal declaration is read through that metavariable
context, and the first goal's local instances are a pragmatic default for
typeclass resolution during graph construction.  A failure is reported as
`graph_v2:null` plus `graph_v2_error`; it never aborts the REPL. -/
private def stateGraphV2 (runtime : Runtime) (state : GoalState)
    (goals : List MVarId) : IO (Json × Option String) := do
  match goals with
  | [] => return (Json.null, none)
  | first :: _ =>
    let coreM := (state.withContext' first (ExprGraphV2.buildGoalStateGraph goals)).run'
    match ← (coreM.run runtime.coreContext { env := runtime.env }).toBaseIO with
    | .ok (graph, _) => return (graph, none)
    | .error exception =>
      let message ← exceptionMessage exception
      return (Json.null, some s!"goal-state v2 graph failed: {message}")

/-- Serialize an arbitrary list of goals using the metavariable context of
    `state`.  We temporarily make that list the tactic goal list because
    Pantograph's serializer reads `GoalState.goals`. -/
private def serializeGoals (runtime : Runtime) (state : GoalState)
    (goals : List MVarId) (graphV2 : Json) (graphV2Error : Option String) :
    IO (Except Exception (Array Json)) := do
  let displayState : GoalState := {
    state with
    savedState := { state.savedState with tactic := { goals := goals } } }
  match ← runMetaM runtime (displayState.serializeGoals (options := {})) with
  | .ok serialized =>
    let mut rendered := #[]
    for index in [:serialized.size] do
      match serialized[index]? with
      | none => pure ()
      | some goal =>
        let (graph, graphError) ← match goals[index]? with
          | some mvar => goalGraph runtime state mvar
          | none => pure (Json.null, some "goal metavariable missing from tracked list")
        rendered := rendered.push
          (goalJson index goal graph graphError graphV2 graphV2Error)
    return .ok rendered
  | .error exception =>
    return .error exception

/-- Build the common `{"status":"ok","goals":...,"solved":...}` response.
    `extra` adds command-specific fields after the common ones. -/
private def stateReply (runtime : Runtime) (session : Session)
    (messages : Array String := #[]) (extra : List (String × Json) := []) :
    IO Json := do
  -- One schema-2 graph covers every goal of the state; it is embedded in each
  -- goal's response (`graph_v2`) together with that goal's `goal_id`/`root`.
  let (graphV2, graphV2Error) ← stateGraphV2 runtime session.state session.goals
  match ← serializeGoals runtime session.state session.goals graphV2 graphV2Error with
  | .ok goals =>
    let solved := session.goals.isEmpty && session.state.isSolved
    return okJson <|
      [("theorem", toJson session.theoremName),
       ("goals", toJson goals),
       ("solved", toJson solved),
       ("messages", toJson messages),
       ("current_goal_roots", Json.arr (currentGoalRootsJson session graphV2))] ++ extra
  | .error exception =>
    let message ← exceptionMessage exception
    return errorJson "tactic_failed" s!"could not serialize goals: {message}"

private def resolveName (theoremName : String) : Name :=
  let raw := theoremName.trimAscii.toString
  let raw := if raw.startsWith "_root_." then (raw.drop 7).toString else raw
  raw.toName

/-- Start a proof from the type of a theorem constant. -/
private def startSession (runtime : Runtime) (theoremName : String) :
    IO (Option Session) := do
  let name := resolveName theoremName
  let some constant := runtime.env.find? name
    | do
      reply <| errorJson "invalid_goal" s!"unknown theorem: {theoremName}"
      return none
  unless constant matches .thmInfo .. do
    reply <| errorJson "invalid_goal" s!"constant is not a theorem: {theoremName}"
    return none
  match ← runTermElabM runtime (m := do
      let state ← GoalState.create constant.type
      Elab.Term.synthesizeSyntheticMVarsUsingDefault
      return state) with
  | .error exception =>
    reply <| errorJson "tactic_failed" (← exceptionMessage exception)
    return none
  | .ok state =>
    let session : Session := {
      state := state
      goals := state.goals
      theoremName := theoremName }
    reply (← stateReply runtime session)
    return some session

/-- A goal selector is either an index into the tracked goal list or the
    metavariable name returned in the `mvar` field. -/
private def parseGoalSelector (json : Json) : Except String (Sum Nat String) := do
  let value ← json.getObjVal? "goal"
  match value with
  | .num _ =>
    return .inl (← value.getNat?)
  | .str name =>
    return .inr name
  | _ =>
    throw "field 'goal' must be a non-negative integer or a metavariable name"

private def parseApplyRequest (json : Json) :
    Except String (Sum Nat String × String) := do
  let selector ← parseGoalSelector json
  let tactic ← json.getObjValAs? String "tactic"
  if tactic.trimAscii.isEmpty then
    throw "field 'tactic' must be a non-empty string"
  return (selector, tactic)

private def resolveGoal (session : Session) (selector : Sum Nat String) :
    Except String MVarId := do
  match selector with
  | .inl index =>
    match session.goals[index]? with
    | some goal => return goal
    | none => throw s!"goal index {index} is out of range (have {session.goals.length} goals)"
  | .inr name =>
    match session.goals.find? (fun goal => goal.name.toString == name) with
    | some goal => return goal
    | none => throw s!"unknown goal metavariable: {name}"

private def failureText (messages : Array Message) : IO String := do
  let rendered ← renderMessages messages
  if rendered.isEmpty then
    return "tactic failed"
  else
    return String.intercalate "\n" rendered.toList

private def handleApply (runtime : Runtime) (session : Session) (json : Json) :
    IO (Option Session) := do
  match parseApplyRequest json with
  | .error message =>
    reply <| errorJson "parse_error" message
    return none
  | .ok (selector, tactic) =>
    match resolveGoal session selector with
    | .error message =>
      reply <| errorJson "invalid_goal" message
      return none
    | .ok goal =>
      match ← runTermElabM runtime (m := session.state.tryTactic (.focus goal) tactic) with
      | .error exception =>
        reply <| errorJson "tactic_failed" (← exceptionMessage exception)
        return none
      | .ok (.failure messages) =>
        reply <| errorJson "tactic_failed" (← failureText messages)
        return none
      | .ok (.parseError message) =>
        reply <| errorJson "parse_error" message
        return none
      | .ok (.invalidAction message) =>
        reply <| errorJson "tactic_failed" message
        return none
      | .ok (.success state messages) =>
        -- The focused tactic only sees `goal`; goals belonging to other
        -- branches stay in our own list.  Drop the focused goal once it is
        -- assigned and add any goals produced by this tactic.
        let survivors := session.goals.filter (· != goal)
        let candidates := mergeGoals survivors state.goals
        let unsolved := candidates.filter fun candidate => !isAssigned state candidate
        let nextSession : Session := {
          state := state
          goals := unsolved
          theoremName := session.theoremName
          snapshots := session.snapshots }
        let renderedMessages ← renderMessages messages
        reply (← stateReply runtime nextSession renderedMessages)
        return some nextSession

/-- Read the required non-empty `name` field of a snapshot request. -/
private def parseSnapshotName (json : Json) : Except String String := do
  let name ← json.getObjValAs? String "name"
  if name.trimAscii.isEmpty then
    throw "field 'name' must be a non-empty string"
  return name

/-- Save the current proof branch under a caller-chosen name. -/
private def handleSnapshot (_runtime : Runtime) (session : Session) (json : Json) :
    IO (Option Session) := do
  match parseSnapshotName json with
  | .error message =>
    reply <| errorJson "parse_error" message
    return none
  | .ok name =>
    let snapshot : Snapshot := { state := session.state, goals := session.goals }
    let nextSession : Session := {
      session with snapshots := session.snapshots.insert name snapshot }
    reply <| okJson [
      ("snapshot", toJson name),
      ("saved", toJson true),
      ("goal_count", toJson session.goals.length)]
    return some nextSession

/-- Restore a previously saved proof branch.  Unknown names leave the current
    branch untouched. -/
private def handleRestore (runtime : Runtime) (session : Session) (json : Json) :
    IO (Option Session) := do
  match parseSnapshotName json with
  | .error message =>
    reply <| errorJson "parse_error" message
    return none
  | .ok name =>
    match session.snapshots[name]? with
    | none =>
      reply <| errorJson "invalid_goal" s!"unknown snapshot: {name}"
      return none
    | some snapshot =>
      let nextSession : Session := {
        session with state := snapshot.state, goals := snapshot.goals }
      reply (← stateReply runtime nextSession (extra := [
        ("snapshot", toJson name), ("restored", toJson true)]))
      return some nextSession

private def handleRequest (runtime : Runtime) (session : Option Session)
    (json : Json) : IO LoopResult := do
  match json.getObjValAs? String "cmd" with
  | .error message =>
    reply <| errorJson "parse_error" s!"missing or invalid 'cmd': {message}"
    return { session := session, stop := false }
  | .ok cmd =>
  match cmd with
    | "start" =>
      match json.getObjValAs? String "theorem" with
      | .error message =>
        reply <| errorJson "parse_error" s!"missing or invalid 'theorem': {message}"
        return { session := session, stop := false }
      | .ok theoremName =>
        let newSession? ← startSession runtime theoremName
        return { session := newSession?, stop := false }
    | "apply" =>
      match session with
      | none =>
        reply <| errorJson "invalid_goal" "no theorem has been started"
        return { session := session, stop := false }
      | some current =>
        let newSession? ← handleApply runtime current json
        let nextSession := match newSession? with
          | some next => some next
          | none => some current
        return { session := nextSession, stop := false }
    | "goals" =>
      match session with
      | none =>
        reply <| errorJson "invalid_goal" "no theorem has been started"
      | some current =>
        reply (← stateReply runtime current)
      return { session := session, stop := false }
    | "snapshot" =>
      match session with
      | none =>
        reply <| errorJson "invalid_goal" "no theorem has been started"
        return { session := session, stop := false }
      | some current =>
        let nextSession? ← handleSnapshot runtime current json
        let nextSession := match nextSession? with
          | some next => some next
          | none => some current
        return { session := nextSession, stop := false }
    | "restore" =>
      match session with
      | none =>
        reply <| errorJson "invalid_goal" "no theorem has been started"
        return { session := session, stop := false }
      | some current =>
        let nextSession? ← handleRestore runtime current json
        let nextSession := match nextSession? with
          | some next => some next
          | none => some current
        return { session := nextSession, stop := false }
    | "close" =>
      reply <| okJson [("closed", toJson true)]
      return { session := session, stop := true }
    | other =>
      reply <| errorJson "parse_error" s!"unknown command: {other}"
      return { session := session, stop := false }

partial def loop (runtime : Runtime) (session : Option Session) : IO UInt32 := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then
    -- EOF: a well-behaved client either sends `close` or closes stdin.
    return 0
  let line := line.trimAscii.toString
  if line.isEmpty then
    loop runtime session
  else
    match Json.parse line with
    | .error message =>
      reply <| errorJson "parse_error" s!"invalid JSON: {message}"
      loop runtime session
    | .ok json =>
      let result ← handleRequest runtime session json
      if result.stop then
        return 0
      else
        loop runtime result.session

end Nazrin.NPARepl

open Nazrin.NPARepl

def main (args : List String) : IO UInt32 := do
  let config : Option (String × String) := match args with
    | [module] => some (module, "200000")
    | [module, heartbeats] => some (module, heartbeats)
    | _ => none
  match config with
  | none =>
    IO.eprintln "Usage: NPARepl MODULE [MAX_HEARTBEATS]"
    return 1
  | some (moduleName, heartbeatLimit) =>
    unsafe Pantograph.initSearch ""
    let env? ← try
        pure (some (← importModules #[{ module := moduleName.toName }] {} 1 (loadExts := true)))
      catch exception =>
        IO.eprintln s!"failed to import {moduleName}: {exception}"
        pure none
    match env? with
    | none => return 1
    | some env =>
      let heartbeatValue := heartbeatLimit.toNat?.getD 200000
      let coreContext ← Pantograph.createCoreContext
        #[s!"maxHeartbeats={heartbeatValue}", "maxRecDepth=8192"]
      let runtime : Runtime := { env := env, coreContext := coreContext }
      reply <| okJson [
        ("ready", toJson true),
        ("module", toJson moduleName),
        ("max_heartbeats", toJson heartbeatValue)]
      loop runtime none
