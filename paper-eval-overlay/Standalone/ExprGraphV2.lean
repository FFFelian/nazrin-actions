/-
  ExprGraphV2: coupled-goal ExprGraph core, JSON schema 2.

  This module is a library module: it deliberately has **no** `main`, so it can
  be imported by exporters and probes without inheriting the `ExprGraphExport`
  CLI.  It builds on the untouched v1 primitives in `GoalGraphCore` /
  `ExprGraphExport` and adds the parts the v1 exporter does not model:

  * one graph for a *set* of goals (a proof state), with `goals[i].root`
    pointing at each goal's target,
  * global fvar nodes: one node per `FVarId`, shared by every goal whose local
    context (or target) mentions it,
  * `fvars[].type_node` / `value_node` for every local declaration,
  * `coupled` groups: connected components of goals that share at least one
    fvar, together with the shared fvar indices,
  * `loci` tagged with their goal id, covering every goal's target positions,
  * `buildConstantGraph`: a schema-2 subgraph for the type (and, when present,
    the definition value) of one constant,
  * `alphaNormalize`: a canonical, metadata-free text form of a graph for
    alpha / search-view comparisons.

  The JSON contract is documented in `experiments/exprgraph/v2/schema-v2.md`.

  Everything v1 does is reused, not re-implemented: node/edge/condensation
  semantics come from `GoalGraphCore.GraphState` and `GoalGraphCore.buildExpr`.
  `Standalone/ExprGraphExport.lean` and `Standalone/GoalGraphCore.lean` are not
  modified.
-/
import Standalone.GoalGraphCore
import Lean.Data.Json

open Lean

namespace ExprGraphV2

/-! ## Reused v1 primitives -/

abbrev GraphState := GoalGraphCore.GraphState
abbrev GoalLocal := GoalGraphCore.GoalLocal
abbrev BuildM := GoalGraphCore.BuildM

/-- Dot-separated `SubExpr.Pos`; the root is the empty string. -/
def posToPath := GoalGraphCore.posToPath

/-- Canonical printed universe level. -/
def levelToString := GoalGraphCore.levelToString

/-- A deterministic, currently unused `3.*` metadata position branch. -/
def freshMetadataPos := GoalGraphCore.freshMetadataPos

/-- A string field extracted from a JSON object without throwing. -/
def jsonStrD (j : Json) (key : String) (default : String := "") : String :=
  match j.getObjValD key with
  | .null => default
  | v => (v.getStr?).toOption.getD default

/-- A natural-number field extracted from a JSON object without throwing. -/
def jsonNatD (j : Json) (key : String) (default : Nat := 0) : Nat :=
  match j.getObjValD key with
  | .null => default
  | v => (v.getNat?).toOption.getD default

/-- A bare JSON value read as a natural number. -/
def jsonAsNatD (j : Json) (default : Nat := 0) : Nat :=
  (j.getNat?).toOption.getD default

/-- An array field, or `#[]` when the field is absent or not an array. -/
def arrFieldD (j : Json) (key : String) : Array Json :=
  match j.getObjValD key with
  | .null => #[]
  | v => (v.getArr?).toOption.getD #[]

/-- A bool field, defaulting to `false`. -/
def jsonBoolD (j : Json) (key : String) (default : Bool := false) : Bool :=
  match j.getObjValD key with
  | .null => default
  | v => (v.getBool?).toOption.getD default

/-! ## Schema 2 data model -/

/-- One goal of a proof state: its stable id and the node id of its target. -/
structure GoalRef where
  /-- Export-local goal identifier (mvar name, disambiguated if duplicated). -/
  goalId : String
  /-- Node id of the essentialized goal target. -/
  root : Nat
  /-- Number of local-context fvars declared by this goal. -/
  fvarCount : Nat := 0

/-- One rewritable subexpression position, scoped to the goal it belongs to. -/
structure Locus where
  goalId : String
  /-- Dot-separated `SubExpr.Pos` relative to the goal target. -/
  position : String
  node : Nat

/-- One free variable of the exported proof state.

`index` is canonical and global: the same `FVarId` has one entry no matter how
many goals mention it.  `goals` lists the goals whose local context declares
it. -/
structure FVarEntry where
  index : Nat
  name : String
  node : Nat
  typeNode : Nat
  valueNode? : Option Nat := none
  goals : Array String := #[]

/-- Condensation table entry: constant name -> shared `const` node. -/
structure ConstEntry where
  name : String
  node : Nat

/-- A set of goals coupled by shared fvars, and the fvars they share. -/
structure CoupledGroup where
  goals : Array String
  fvars : Array Nat

/-- A schema-2 ExprGraph: a proof state (or one constant) as a typed
heterogeneous graph.  `toJson` is the single source of truth for the wire
format. -/
structure ExprGraphV2 where
  /-- Theorem name (JSON field `theorem`), or `""` when the caller did not
  supply provenance. -/
  theoremName : String := ""
  /-- Declaring module, when known. -/
  module? : Option String := none
  /-- Constant name for definition graphs; absent for proof-state graphs. -/
  constant? : Option String := none
  goals : Array GoalRef := #[]
  nodes : Array Json := #[]
  edges : Array Json := #[]
  loci : Array Locus := #[]
  fvars : Array FVarEntry := #[]
  constants : Array ConstEntry := #[]
  coupled : Array CoupledGroup := #[]
  parseWarnings : Array String := #[]

/-- The schema number emitted by `ExprGraphV2.toJson`. -/
def schemaVersion : Nat := 2

namespace GoalRef

def toJson (g : ExprGraphV2.GoalRef) : Lean.Json :=
  Lean.Json.mkObj [
    ("goal_id", Lean.toJson g.goalId),
    ("root", Lean.toJson g.root),
    ("fvar_count", Lean.toJson g.fvarCount)]

end GoalRef

namespace Locus

def toJson (l : ExprGraphV2.Locus) : Lean.Json :=
  Lean.Json.mkObj [
    ("goal_id", Lean.toJson l.goalId),
    ("position", Lean.toJson l.position),
    ("node", Lean.toJson l.node)]

end Locus

namespace FVarEntry

def toJson (f : ExprGraphV2.FVarEntry) : Lean.Json :=
  Lean.Json.mkObj <|
    [("index", Lean.toJson f.index), ("name", Lean.toJson f.name),
     ("node", Lean.toJson f.node), ("type_node", Lean.toJson f.typeNode)] ++
    (match f.valueNode? with
     | some vn => [("value_node", Lean.toJson vn)]
     | none => []) ++
    [("goals", Lean.Json.arr (f.goals.map Lean.toJson))]

end FVarEntry

namespace ConstEntry

def toJson (c : ExprGraphV2.ConstEntry) : Lean.Json :=
  Lean.Json.mkObj [("name", Lean.toJson c.name), ("node", Lean.toJson c.node)]

end ConstEntry

namespace CoupledGroup

def toJson (c : ExprGraphV2.CoupledGroup) : Lean.Json :=
  Lean.Json.mkObj [
    ("goals", Lean.Json.arr (c.goals.map Lean.toJson)),
    ("fvars", Lean.Json.arr (c.fvars.map Lean.toJson))]

end CoupledGroup

/-- Serialize to the schema-2 JSON object.  Field order is fixed, so
`Json.compress` output is byte-stable for a fixed graph. -/
def toJson (g : ExprGraphV2) : Json :=
  let provenance : List (String × Json) :=
    [("schema", Lean.toJson schemaVersion), ("theorem", Lean.toJson g.theoremName)] ++
    (match g.module? with
     | some m => [("module", Lean.toJson m)]
     | none => []) ++
    (match g.constant? with
     | some c => [("constant", Lean.toJson c)]
     | none => [])
  Json.mkObj <|
    provenance ++
    [("goals", Json.arr (g.goals.map GoalRef.toJson)),
     ("nodes", Json.arr g.nodes),
     ("edges", Json.arr g.edges),
     ("loci", Json.arr (g.loci.map Locus.toJson)),
     ("fvars", Json.arr (g.fvars.map FVarEntry.toJson)),
     ("constants", Json.arr (g.constants.map ConstEntry.toJson)),
     ("coupled", Json.arr (g.coupled.map CoupledGroup.toJson)),
     ("parse_warnings", Json.arr (g.parseWarnings.map Lean.toJson))]

/-- Graph-level counts.  Used by the exporter/README statistics and by tests to
cross-check the Python validator. -/
def stats (graph : Json) : Except String Json := do
  let goals := arrFieldD graph "goals"
  let nodes := arrFieldD graph "nodes"
  let edges := arrFieldD graph "edges"
  let loci := arrFieldD graph "loci"
  let fvars := arrFieldD graph "fvars"
  let constants := arrFieldD graph "constants"
  let coupled := arrFieldD graph "coupled"
  let shared := fvars.filter fun f => (arrFieldD f "goals").size ≥ 2
  let coupling := Array.foldl (fun acc c => acc + (arrFieldD c "goals").size) 0 coupled
  let couplingFvars := Array.foldl (fun acc c => acc + (arrFieldD c "fvars").size) 0 coupled
  return Json.mkObj [
    ("goals", Lean.toJson goals.size),
    ("nodes", Lean.toJson nodes.size),
    ("edges", Lean.toJson edges.size),
    ("loci", Lean.toJson loci.size),
    ("fvars", Lean.toJson fvars.size),
    ("shared_fvars", Lean.toJson shared.size),
    ("coupled_groups", Lean.toJson coupled.size),
    ("coupled_goals", Lean.toJson coupling),
    ("coupled_fvars", Lean.toJson couplingFvars),
    ("constants", Lean.toJson constants.size)]

/-! ## Build state

The build state wraps the v1 `GraphState` (condensation maps, loci, edges) and
adds the multi-goal bookkeeping: per-goal node/locus ranges, the global fvar
table, and accumulated warnings. -/

/-- One goal as it was actually built.  `nodeStart..nodeEnd` and
`lociStart..lociEnd` are slices of the shared graph state. -/
structure GoalBuild where
  goalId : String
  root : Nat
  fvarIds : Array FVarId
  nodeStart : Nat
  nodeEnd : Nat
  lociStart : Nat
  lociEnd : Nat
deriving Inhabited

/-- Mutable state of one schema-2 build. -/
structure BuildState where
  graph : GraphState := {}
  goals : Array GoalBuild := #[]
  fvarEntries : Array FVarEntry := #[]
  fvarOrder : Array FVarId := #[]
  fvarIndex : Std.HashMap FVarId Nat := {}
  fvarTyped : Std.HashSet FVarId := {}
  warnings : Array String := #[]

abbrev V2M := StateM BuildState

/-- Run a v1 graph action against the embedded `GraphState`. -/
def liftG {α : Type} (m : BuildM α) : V2M α := fun s =>
  let (a, g) := m s.graph
  (a, { s with graph := g })

/-- Build a metadata-only subgraph: it must not pollute the goal's locus table,
exactly as in the v1 goal exporter. -/
def withLociOff {α : Type} (m : V2M α) : V2M α := fun s =>
  let (a, s') := m { s with graph := { s.graph with trackLoci := false } }
  (a, { s' with graph := { s'.graph with trackLoci := s.graph.trackLoci } })

def addLocusV2 (pos : SubExpr.Pos) (node : Nat) : V2M Unit :=
  liftG (GoalGraphCore.addLocus pos node)

def warn (message : String) : V2M Unit :=
  modify fun s => { s with warnings := s.warnings.push message }

/-- One goal prepared for graph construction. -/
structure GoalInput where
  goalId : String
  target : Expr
  locals : Array GoalLocal := #[]

/-- Create (or reuse) the fvar node of `loc`, and — the first time this
`FVarId` is seen — build the graph of its type and optional let-value.

Sharing is keyed on `FVarId`, so one fvar mentioned by several goals gets exactly
one node and one `type_node`; the `fvar_type` edge is emitted once. -/
def ensureFVar (loc : GoalLocal) : V2M Unit := do
  let s0 ← get
  let nodePos := freshMetadataPos s0.graph
  let node ← liftG (GoalGraphCore.getOrCreateFVar loc.fvarId nodePos 0)
  if (← get).fvarTyped.contains loc.fvarId then
    return ()
  let typePos := freshMetadataPos (← get).graph
  let typeNode ← withLociOff (liftG (GoalGraphCore.buildExpr loc.type typePos 0))
  liftG (GoalGraphCore.addEdge node typeNode "fvar_type")
  if loc.nondep then
    warn s!"local declaration {loc.name} is a non-dependent let; its value is opaque and may be type-incorrect"
  let mut valueNode? : Option Nat := none
  if let some value := loc.value? then
    let valuePos := freshMetadataPos (← get).graph
    let valueNode ← withLociOff (liftG (GoalGraphCore.buildExpr value valuePos 0))
    liftG (GoalGraphCore.addEdge node valueNode "fvar_value")
    valueNode? := some valueNode
  let s ← get
  let index := s.fvarEntries.size
  let displayName := if loc.displayName.isEmpty then loc.name.toString else loc.displayName
  set { s with
    fvarEntries := s.fvarEntries.push {
      index := index
      name := displayName
      node := node
      typeNode := typeNode
      valueNode? := valueNode? }
    fvarOrder := s.fvarOrder.push loc.fvarId
    fvarIndex := s.fvarIndex.insert loc.fvarId index
    fvarTyped := s.fvarTyped.insert loc.fvarId }

/-- Build one goal: target graph (locus-tracked), then its local declarations
(metadata, locus-free). -/
def buildGoal (input : GoalInput) : V2M Unit := do
  let start ← get
  let nodeStart := start.graph.nodes.size
  let lociStart := start.graph.loci.size
  let root ← liftG (GoalGraphCore.buildExpr input.target .root 0)
  addLocusV2 .root root
  for loc in input.locals do
    ensureFVar loc
  let fvarIds : Array FVarId := input.locals.map fun loc => loc.fvarId
  let s ← get
  set { s with
    goals := s.goals.push {
      goalId := input.goalId
      root := root
      fvarIds := fvarIds
      nodeStart := nodeStart
      nodeEnd := s.graph.nodes.size
      lociStart := lociStart
      lociEnd := s.graph.loci.size } }

/-- Pure build of a multi-goal state. -/
def buildGoalState (inputs : Array GoalInput) : BuildState :=
  let (_, s) := (Array.forM buildGoal inputs).run {}
  s

/-! ## Finalization: coupled groups, loci, fvar table -/

/-- The goal that created `node`, if it lies in a recorded range. -/
def nodeOwner (goals : Array GoalBuild) (node : Nat) : Option String :=
  goals.findSome? fun g =>
    if g.nodeStart ≤ node && node < g.nodeEnd then some g.goalId else none

/-- Goals whose local context declares `fvarId`, in goal order. -/
def fvarGoals (goals : Array GoalBuild) (fvarId : FVarId) : Array String :=
  Array.filterMap (fun g => if g.fvarIds.contains fvarId then some g.goalId else none) goals

/-- Loci are stored untagged inside `GraphState`; tag each goal's slice with its
goal id so that `(goal, position)` is the unique key. -/
def lociOf (s : BuildState) : Array Locus := Id.run do
  let mut loci : Array Locus := #[]
  for g in s.goals do
    for entry in s.graph.loci.extract g.lociStart g.lociEnd do
      loci := loci.push {
        goalId := g.goalId
        position := jsonStrD entry "position"
        node := jsonNatD entry "node" }
  return loci

/-- Coupled-goal structure.

Two goals are *coupled* when they share at least one fvar; this is the paper's
"coupled goals" requirement, implemented here as shared variable identity across
goals (an explicit implementation choice, see the README).  The result is the
connected-component decomposition of that relation: one entry per component of
size >= 2, listing the component's goals and every fvar shared by at least two
goals of the component. -/
def coupledGroups (goals : Array GoalBuild) (fvarIndex : Std.HashMap FVarId Nat) :
    Array CoupledGroup := Id.run do
  let n := goals.size
  if n < 2 then return #[]
  let mut occurrences : Std.HashMap FVarId (Array Nat) := {}
  for i in [:n] do
    for fvarId in goals[i]!.fvarIds do
      occurrences := occurrences.insert fvarId ((occurrences.getD fvarId #[]).push i)
  let mut adjacency : Array (Array Nat) := Array.replicate n #[]
  for (_fvarId, gs) in occurrences.toList do
    if gs.size ≥ 2 then
      for j in gs do
        for k in gs do
          if j != k then
            adjacency := adjacency.set! j ((adjacency[j]!).push k)
  let mut visited : Array Bool := Array.replicate n false
  let mut groups : Array CoupledGroup := #[]
  for start in [:n] do
    unless visited[start]! do
      let mut stack : Array Nat := #[start]
      visited := visited.set! start true
      let mut component : Array Nat := #[]
      while !stack.isEmpty do
        let i := stack.back!
        stack := stack.pop
        component := component.push i
        for j in adjacency[i]! do
          unless visited[j]! do
            visited := visited.set! j true
            stack := stack.push j
      if component.size ≥ 2 then
        let sortedComponent := component.qsort (· < ·)
        let shared : Array Nat := Array.filterMap
          (fun (fvarId, gs) =>
            if gs.size ≥ 2 && sortedComponent.all (fun i => gs.contains i) then
              fvarIndex[fvarId]?
            else none)
          occurrences.toList.toArray
        groups := groups.push {
          goals := sortedComponent.map (fun i => goals[i]!.goalId)
          fvars := shared.qsort (· < ·) }
  return groups

/-- Assemble the public `ExprGraphV2` value from a finished build state. -/
def finalize (s : BuildState) (theoremName : String) (moduleName : Option String)
    (constantName : Option String) (warnings : Array String) : ExprGraphV2 :=
  let goals : Array GoalRef := s.goals.map fun g =>
    { goalId := g.goalId, root := g.root, fvarCount := g.fvarIds.size }
  let nodes := s.graph.nodes.mapIdx fun node json =>
    json.setObjVal! "goal" (Lean.toJson ((nodeOwner s.goals node).getD ""))
  let fvars : Array FVarEntry := s.fvarEntries.map fun entry =>
    { entry with goals := fvarGoals s.goals (s.fvarOrder[entry.index]!) }
  let constants : Array ConstEntry := s.graph.constList.map fun (name, node) =>
    { name := name.toString, node := node }
  { theoremName := theoremName
    module? := moduleName
    constant? := constantName
    goals := goals
    nodes := nodes
    edges := s.graph.edges
    loci := lociOf s
    fvars := fvars
    constants := constants
    coupled := coupledGroups s.goals s.fvarIndex
    parseWarnings := warnings }

/-! ## Goal preparation (MetaM) -/

/-- Deterministic, globally unique display names for every fvar of every goal.

Lean allows duplicate user names (several `x` hypotheses, and the same name in
two goals); `fvars[].name` must be unique so downstream pointers are
unambiguous.  The first occurrence keeps the user name, later ones get
`name#1`, `name#2`, ... in goal order, then local-context order. -/
def displayNamesFor (contexts : Array LocalContext) : Std.HashMap FVarId String := Id.run do
  let mut used : Std.HashSet String := {}
  let mut nextSuffix : Std.HashMap String Nat := {}
  let mut names : Std.HashMap FVarId String := {}
  for lctx in contexts do
    for ldecl in lctx do
      unless names.contains ldecl.fvarId do
        let base := ldecl.userName.toString
        let mut display := base
        if used.contains display then
          let mut index := nextSuffix.getD base 1
          display := s!"{base}#{index}"
          while used.contains display do
            index := index + 1
            display := s!"{base}#{index}"
          nextSuffix := nextSuffix.insert base (index + 1)
        used := used.insert display
        names := names.insert ldecl.fvarId display
  return names

/-- Make goal ids unique (`name`, `name#1`, ...) and non-empty. -/
def uniqueGoalIds (ids : Array String) : Array String := Id.run do
  let mut used : Std.HashSet String := {}
  let mut out : Array String := #[]
  for id in ids do
    let base := if id.isEmpty then "goal" else id
    let mut display := base
    let mut index := 1
    while used.contains display do
      display := s!"{base}#{index}"
      index := index + 1
    used := used.insert display
    out := out.push display
  return out

/-- Instantiate a goal target and its local declarations for graph
construction, collecting warnings instead of failing. -/
def prepareGoalInput (mvarId : MVarId) (goalId : String)
    (names : Std.HashMap FVarId String) : MetaM (GoalInput × Array String) := do
  let decl ← mvarId.getDecl
  let (target, targetWarnings) ←
    GoalGraphCore.instantiateForGraph (← mvarId.getType) s!"goal {goalId}: target"
  let mut warnings := targetWarnings
  if target.isMVar then
    warnings := warnings.push s!"goal {goalId}: target is an unresolved metavariable"
  let mut locals : Array GoalLocal := #[]
  for ldecl in decl.lctx do
    let (type, typeWarnings) ←
      GoalGraphCore.instantiateForGraph ldecl.type s!"goal {goalId}: local {ldecl.userName}"
    warnings := warnings ++ typeWarnings
    let value? ← match ldecl.value? with
      | none => pure none
      | some value =>
        let (value, valueWarnings) ←
          GoalGraphCore.instantiateForGraph value s!"goal {goalId}: local {ldecl.userName} value"
        warnings := warnings ++ valueWarnings
        pure (some value)
    locals := locals.push {
      fvarId := ldecl.fvarId
      name := ldecl.userName
      type := type
      value? := value?
      isLet := ldecl.isLet true
      nondep := match ldecl with
        | .ldecl (nondep := nondep) .. => nondep
        | .cdecl .. => false }
  locals := locals.map fun loc =>
    { loc with displayName := names[loc.fvarId]?.getD loc.name.toString }
  return ({ goalId := goalId, target := target, locals := locals }, warnings)

/-! ## Goal-state entry points -/

/-- Build a schema-2 proof-state graph for explicit `(goalId, mvar)` pairs,
returning the JSON and every non-fatal warning.

Failures and unsupported structures are reported in `parse_warnings`; nothing is
silently dropped.  An empty goal list yields `goals: []` plus a warning (and is
rejected by `validate_exprgraph_v2.py`). -/
def buildGoalStateGraphNamedFull (theoremName : String) (moduleName : Option String)
    (goals : Array (String × MVarId)) : MetaM (Json × Array String) := do
  let ids := uniqueGoalIds (goals.map fun (id, _) => id)
  let goals := goals.zip ids |>.map fun ((_, mvarId), id) => (id, mvarId)
  let decls ← Array.mapM (fun (_, mvarId) => mvarId.getDecl) goals
  let names := displayNamesFor (decls.map (·.lctx))
  let mut inputs : Array GoalInput := #[]
  let mut warnings : Array String := #[]
  for (goalId, mvarId) in goals do
    let (input, goalWarnings) ← prepareGoalInput mvarId goalId names
    inputs := inputs.push input
    warnings := warnings ++ goalWarnings
  if inputs.isEmpty then
    warnings := warnings.push "goal-state graph requested without goals"
  let state := buildGoalState inputs
  warnings := warnings ++ state.warnings
  let mut lctxFvars : Std.HashSet FVarId := {}
  for g in state.goals do
    for fvarId in g.fvarIds do
      lctxFvars := lctxFvars.insert fvarId
  for (fvarId, _) in state.graph.fvarList do
    unless lctxFvars.contains fvarId do
      warnings := warnings.push
        s!"fvar {fvarId.name} occurs in a goal target but belongs to no exported local context"
  let graph := finalize state theoremName moduleName none warnings
  return (ExprGraphV2.toJson graph, warnings)

/-- **Coupled-goal entry point.**  Build the schema-2 graph of a proof state
given its goals.  Goal ids default to the metavariable names; the `theorem`
field is empty because no provenance was supplied (use
`buildGoalStateGraphJson` when a theorem name is available). -/
def buildGoalStateGraph (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFull "" none pairs).1

/-- Goal-state graph with an explicit theorem name. -/
def buildGoalStateGraphAs (theoremName : Name) (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFull theoremName.toString none pairs).1

/-- Goal-state graph with theorem and module provenance. -/
def buildGoalStateGraphJson (theoremName : Name) (moduleName : String)
    (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFull theoremName.toString (some moduleName) pairs).1

/-- Goal-state graph with theorem provenance, also returning the warnings. -/
def buildGoalStateGraphFull (theoremName : Name) (goals : List MVarId) :
    MetaM (Json × Array String) := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return ← buildGoalStateGraphNamedFull theoremName.toString none pairs

/-! ## Constant (definition) graphs -/

/-- Which value (if any) a constant graph includes.

`theorem` proofs are excluded by default: a proof term is a proof, not a
definition, and can dwarf the type graph.  Set `includeTheoremProof := true`
to export it anyway. -/
structure ConstantGraphConfig where
  /-- Include the value of `def`/`abbrev`/`opaque` constants. -/
  includeValue : Bool := true
  /-- Include the proof term of `theorem` constants. -/
  includeTheoremProof : Bool := false

/-- The definition body to export, according to `cfg`. -/
def constantValue? (cfg : ConstantGraphConfig) : ConstantInfo → Option Expr
  | .defnInfo v => if cfg.includeValue then some v.value else none
  | .opaqueInfo v => if cfg.includeValue then some v.value else none
  | .thmInfo v => if cfg.includeTheoremProof then some v.value else none
  | _ => none

/-- Goal ids used by constant graphs; they live in the same `goals` array so a
consumer needs no second root convention. -/
def constantTypeGoalId : String := "constant:type"

/-- Goal id of the value root of a constant graph. -/
def constantValueGoalId : String := "constant:value"

/-- Build a schema-2 graph for one constant's type (and value, when present and
enabled), returning the warnings.  Unknown constants and export failures return
`none` plus a warning instead of throwing. -/
def buildConstantGraphWith (cfg : ConstantGraphConfig) (name : Name) :
    MetaM (Option Json × Array String) := do
  try
    match (← getEnv).find? name with
    | none =>
      let warning := s!"constant graph: constant {name} is not in the environment"
      logWarning m!"{warning}"
      return (none, #[warning])
    | some info =>
      let (type, typeWarnings) ←
        GoalGraphCore.instantiateForGraph info.type s!"constant {name}: type"
      let mut warnings := typeWarnings
      let mut inputs : Array GoalInput :=
        #[{ goalId := constantTypeGoalId, target := type }]
      if let some value := constantValue? cfg info then
        let (value, valueWarnings) ←
          GoalGraphCore.instantiateForGraph value s!"constant {name}: value"
        warnings := warnings ++ valueWarnings
        inputs := inputs.push { goalId := constantValueGoalId, target := value }
      let state := buildGoalState inputs
      warnings := warnings ++ state.warnings
      let graph := finalize state "" none (some name.toString) warnings
      return (some (ExprGraphV2.toJson graph), warnings)
  catch ex =>
    let message ← ex.toMessageData.toString
    let warning := s!"constant graph: failed for {name}: {message}"
    logWarning m!"{warning}"
    return (none, #[warning])

/-- `buildConstantGraphWith` with the default configuration, plus warnings. -/
def buildConstantGraphFull (name : Name) : MetaM (Option Json × Array String) :=
  buildConstantGraphWith {} name

/-- **Definition-graph entry point.**  Build the schema-2 subgraph of one
constant from the environment: its type, plus its value for definitions.  The
result carries `constant: <name>` and a `constant:type` goal (and a
`constant:value` goal when a value was exported).

Returns `none` when the constant is unknown or cannot be exported; a warning is
logged in that case (and returned by `buildConstantGraphFull`). -/
def buildConstantGraph (name : Name) : MetaM (Option Json) :=
  return (← buildConstantGraphWith {} name).1

/-! ## Essentialization and search-view approximation

`essentialize` is the v1 instantiation pipeline (`Nazrin.instantiateAll`:
instantiate delayed metavariables, unfold internal/auxiliary definitions and
matchers).  `searchViewNormalize` is an *approximation* of the paper's
search-view equivalence; its exact boundary is documented in
`experiments/exprgraph/v2/README.md`. -/

/-- Essentialize an expression for graph construction: instantiate
metavariables and unfold internal definitions.  On failure the input expression
is returned unchanged together with a warning (never silently replaced). -/
def essentialize (e : Expr) (label : String := "expression") : MetaM (Expr × Array String) :=
  GoalGraphCore.instantiateForGraph e label

/-- Erase `Expr.mdata` presentation wrappers recursively. -/
partial def eraseMData (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => eraseMData inner
  | .app fn arg => .app (eraseMData fn) (eraseMData arg)
  | .lam name type body info => .lam name (eraseMData type) (eraseMData body) info
  | .forallE name type body info => .forallE name (eraseMData type) (eraseMData body) info
  | .letE name type value body nondep =>
    .letE name (eraseMData type) (eraseMData value) (eraseMData body) nondep
  | .proj structName fieldIndex inner => .proj structName fieldIndex (eraseMData inner)
  | other => other

/-- Approximate search-view normalization of a term.

Applied transformations (all documented in the v2 README):
1. `mdata` erasure (the graph builder already ignores `mdata`);
2. binder info reset to `BinderInfo.default` (the graph never stores it);
3. zeta-reduction of `letE` (substitute the value into the body).

Deliberately **not** applied: `whnf`/delta reduction of arbitrary constants,
beta/eta reduction, universe-parameter canonicalization, `simp`-style
normalization.  So this is strictly weaker than definitional equality and must
not be treated as a decision procedure for the paper's search-view
equivalence. -/
partial def searchViewNormalizeExpr (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => searchViewNormalizeExpr inner
  | .app fn arg => .app (searchViewNormalizeExpr fn) (searchViewNormalizeExpr arg)
  | .lam name type body _ =>
    .lam name (searchViewNormalizeExpr type) (searchViewNormalizeExpr body) .default
  | .forallE name type body _ =>
    .forallE name (searchViewNormalizeExpr type) (searchViewNormalizeExpr body) .default
  | .letE _ _valueType value body _ =>
    (searchViewNormalizeExpr body).instantiate1 (searchViewNormalizeExpr value)
  | .proj structName fieldIndex inner =>
    .proj structName fieldIndex (searchViewNormalizeExpr inner)
  | other => other

/-- Essentialize, then apply the documented search-view approximation. -/
def searchViewNormalize (e : Expr) (label : String := "expression") :
    MetaM (Expr × Array String) := do
  let (e', warnings) ← essentialize e label
  return (searchViewNormalizeExpr e', warnings)

/-! ## Canonical form: `alphaNormalize`

The canonical form drops every name/position-bearing metadata field
(`theorem`, `module`, `goals[].goal_id`, `fvars[].name`, every node
`position`/`depth`, every locus position, `parse_warnings`), renumbers nodes by
a deterministic traversal from the goal roots, renumbers fvars by first
occurrence in that traversal, and prints one line per fact.  Two graphs are
alpha-equivalent (and, to the extent the builder's search-view approximation
holds, search-view equivalent) exactly when their canonical forms are equal.

`coupled` groups are reduced to canonical goal indices and canonical fvar
indices, so a coupled group survives normalization without any user name.
-/

/-- Node fields that participate in the canonical form.  Condensed atoms keep
their semantic payload (constant name, universe levels, sort, literal, de
Bruijn index, projection); fvar/mvar payloads are replaced by canonical
indices. -/
structure RawNode where
  kind : String := "unknown"
  constName : String := ""
  level : Array String := #[]
  sort : String := ""
  lit : String := ""
  litType : String := ""
  bvar : Nat := 0
  fvarIdx : Nat := 0
  mvarIdx : Nat := 0
  projStruct : String := ""
  projField : Nat := 0
deriving Inhabited

/-- Read one node object into `RawNode` without throwing. -/
def rawNodeOf (j : Json) : RawNode :=
  { kind := jsonStrD j "kind" "unknown"
    constName := jsonStrD j "const"
    level := (arrFieldD j "level").map fun v => (v.getStr?).toOption.getD ""
    sort := jsonStrD j "sort"
    lit := jsonStrD j "lit"
    litType := jsonStrD j "litType"
    bvar := jsonNatD j "bvar"
    fvarIdx := jsonNatD j "fvar"
    mvarIdx := jsonNatD j "mvar"
    projStruct := jsonStrD j "projStruct"
    projField := jsonNatD j "projField" }

/-- Fixed relation order; used for deterministic child traversal and edge
output. -/
def edgeRank : String → Nat
  | "app_fn" => 0
  | "app_arg" => 1
  | "binder_type" => 2
  | "binder_body" => 3
  | "let_type" => 4
  | "let_value" => 5
  | "let_body" => 6
  | "proj_struct" => 7
  | "fvar_type" => 8
  | "fvar_value" => 9
  | _ => 10

/-- One parsed edge: source node, relation, target node. -/
structure RawEdge where
  src : Nat
  type : String
  dst : Nat

/-- Typed adjacency, children sorted by relation rank. -/
def adjacencyOf (nodeCount : Nat) (edges : Array RawEdge) : Array (Array (String × Nat)) := Id.run do
  let mut adjacency : Array (Array (String × Nat)) := Array.replicate nodeCount #[]
  for edge in edges do
    if edge.src < nodeCount && edge.dst < nodeCount then
      adjacency := adjacency.set! edge.src ((adjacency[edge.src]!).push (edge.type, edge.dst))
  let mut sorted : Array (Array (String × Nat)) := Array.replicate nodeCount #[]
  for i in [:nodeCount] do
    sorted := sorted.set! i ((adjacency[i]!).qsort (fun a b => edgeRank a.1 < edgeRank b.1))
  return sorted

/-- Canonical traversal state. -/
structure CanonState where
  canon : Std.HashMap Nat Nat := {}
  order : Array Nat := #[]
  fvarCanon : Std.HashMap Nat Nat := {}
  fvarNodes : Array Nat := #[]
  mvarCanon : Std.HashMap Nat Nat := {}
  mvarNodes : Array Nat := #[]

/-- Iterative pre-order DFS from `stack`, assigning canonical node ids (and
canonical fvar/mvar indices) on first visit. -/
partial def dfsVisit (nodes : Array RawNode) (adjacency : Array (Array (String × Nat)))
    (stack : List Nat) (st : CanonState) : CanonState :=
  match stack with
  | [] => st
  | node :: rest =>
    if st.canon.contains node then
      dfsVisit nodes adjacency rest st
    else
      let id := st.order.size
      let kind := if node < nodes.size then nodes[node]!.kind else "unknown"
      let st1 : CanonState :=
        { st with canon := st.canon.insert node id, order := st.order.push node }
      let st2 : CanonState :=
        if kind == "fvar" then
          { st1 with
            fvarCanon := st1.fvarCanon.insert node st1.fvarNodes.size
            fvarNodes := st1.fvarNodes.push node }
        else if kind == "mvar" then
          { st1 with
            mvarCanon := st1.mvarCanon.insert node st1.mvarNodes.size
            mvarNodes := st1.mvarNodes.push node }
        else st1
      let children :=
        if node < adjacency.size then (adjacency[node]!).map (·.2) |>.toList else []
      dfsVisit nodes adjacency (children ++ rest) st2

/-- Goal table: `(goal_id, root)` in declaration order.  A schema-1 graph (no
`goals` array) is treated as a single anonymous goal rooted at `root`. -/
def goalTableOf (graph : Json) : Array (String × Nat) :=
  let goals := arrFieldD graph "goals"
  if goals.isEmpty then
    #[("", jsonNatD graph "root" 0)]
  else
    goals.map fun g => (jsonStrD g "goal_id" "", jsonNatD g "root" 0)

/-- Fvar table: `(index, node, type_node, value_node?)`. -/
def fvarTableOf (graph : Json) : Array (Nat × Nat × Nat × Option Nat) :=
  (arrFieldD graph "fvars").map fun f =>
    (jsonNatD f "index", jsonNatD f "node", jsonNatD f "type_node",
     if (f.getObjValD "value_node").isNull then none else some (jsonNatD f "value_node"))

/-- Constant table: `(name, node)`. -/
def constantTableOf (graph : Json) : Array (String × Nat) :=
  (arrFieldD graph "constants").map fun c => (jsonStrD c "name", jsonNatD c "node")

/-- Index of `goalId` in `goals`, if present. -/
def goalIndexOf (goals : Array (String × Nat)) (goalId : String) : Option Nat :=
  goals.findIdx? (fun (id, _) => id == goalId)

/-- Payload of a node in the canonical form. -/
def nodePayload (node : RawNode) (st : CanonState) (orig : Nat) : String :=
  match node.kind with
  | "const" => s!"{node.constName}[{String.intercalate "," node.level.toList}]"
  | "sort" => node.sort
  | "lit" => s!"{node.litType}:{node.lit}"
  | "bvar" => s!"bvar{node.bvar}"
  | "fvar" => s!"fvar{st.fvarCanon.getD orig node.fvarIdx}"
  | "mvar" => s!"mvar{st.mvarCanon.getD orig node.mvarIdx}"
  | "proj" => s!"{node.projStruct}.{node.projField}"
  | _ => "-"

/-- Sort a `Nat × Nat` array by first, then second component. -/
def sortPairs (pairs : Array (Nat × Nat)) : Array (Nat × Nat) :=
  pairs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- Canonical, metadata-free text form of a schema-2 (or schema-1) graph.

The output is stable across: goal ids, fvar display names, theorem/module
provenance, node numbering, and fvar numbering.  It keeps: node kinds and
semantic payloads, edge relations, the per-goal root structure, the constant
table, the fvar table (type/value nodes), coupled groups, and the
`(goal, node)` locus multiset. -/
def alphaNormalize (graph : Json) : Except String String := do
  let nodeJson := arrFieldD graph "nodes"
  let nodes : Array RawNode := nodeJson.map rawNodeOf
  let edges : Array RawEdge := (arrFieldD graph "edges").map fun e =>
    { src := jsonNatD e "src", type := jsonStrD e "type", dst := jsonNatD e "dst" }
  let adjacency := adjacencyOf nodes.size edges
  let goals := goalTableOf graph
  let fvarTable := fvarTableOf graph
  let constantTable := constantTableOf graph
  let roots := goals.map (·.2)
  let mut st := dfsVisit nodes adjacency roots.toList {}
  for (_index, node, typeNode, valueNode?) in fvarTable do
    st := dfsVisit nodes adjacency [node, typeNode] st
    if let some value := valueNode? then
      st := dfsVisit nodes adjacency [value] st
  for i in [:nodes.size] do
    st := dfsVisit nodes adjacency [i] st
  let canon := fun (n : Nat) => st.canon.getD n n
  let mut lines : Array String := #["exprgraph-v2-canonical"]
  if !(graph.getObjValD "constant").isNull then
    lines := lines.push s!"constant {jsonStrD graph "constant" ""}"
  lines := lines.push s!"goals {goals.size}"
  for i in [:goals.size] do
    lines := lines.push s!"goal {i} root {canon goals[i]!.2}"
  for i in [:st.order.size] do
    let orig := st.order[i]!
    let node := if orig < nodes.size then nodes[orig]! else {}
    lines := lines.push s!"node {i} {node.kind} {nodePayload node st orig}"
  for i in [:st.order.size] do
    let orig := st.order[i]!
    for (edgeType, dst) in (if orig < adjacency.size then adjacency[orig]! else #[]) do
      lines := lines.push s!"edge {i} {edgeType} {canon dst}"
  for (name, node) in constantTable.qsort (fun a b => a.1 < b.1) do
    lines := lines.push s!"const {name} {canon node}"
  let mut fvarIndexToCanon : Std.HashMap Nat Nat := {}
  let mut fvarLines : Array (Nat × Nat × Nat × Option Nat) := #[]
  for (index, node, typeNode, valueNode?) in fvarTable do
    let canonIndex := st.fvarCanon.getD node index
    fvarIndexToCanon := fvarIndexToCanon.insert index canonIndex
    fvarLines := fvarLines.push (canonIndex, canon node, canon typeNode,
      valueNode?.map canon)
  for (index, node, typeNode, valueNode?) in
      fvarLines.qsort (fun a b => a.1 < b.1) do
    let base := s!"fvar {index} node {node} type {typeNode}"
    match valueNode? with
    | some value => lines := lines.push s!"{base} value {value}"
    | none => lines := lines.push base
  for entry in arrFieldD graph "mvars" do
    let node := jsonNatD entry "node"
    lines := lines.push s!"mvar {st.mvarCanon.getD node (jsonNatD entry "index")} node {canon node}"
  for group in arrFieldD graph "coupled" do
    -- `coupled[].goals` is an array of JSON strings, not of objects: read each
    -- entry with `getStr?` (using `jsonStrD` here would return "" for every
    -- goal and silently drop the whole group from the canonical form).
    let goalIndices : Array Nat := Array.filterMap
      (fun g => goalIndexOf goals ((g.getStr?).toOption.getD "")) (arrFieldD group "goals")
    let fvarIndices : Array Nat := Array.filterMap
      (fun v => fvarIndexToCanon[jsonAsNatD v]?) (arrFieldD group "fvars")
    let join (xs : Array Nat) : String := String.intercalate "," (xs.map toString).toList
    lines := lines.push
      s!"coupled [{join (goalIndices.qsort (· < ·))}] [{join (fvarIndices.qsort (· < ·))}]"
  let mut locusPairs : Array (Nat × Nat) := #[]
  for entry in arrFieldD graph "loci" do
    let goalIndex := goalIndexOf goals (jsonStrD entry "goal_id" "") |>.getD 0
    locusPairs := locusPairs.push (goalIndex, canon (jsonNatD entry "node"))
  for (goalIndex, node) in sortPairs locusPairs do
    lines := lines.push s!"locus {goalIndex} {node}"
  return String.intercalate "\n" lines.toList

/-- Two graphs are alpha-equivalent when their canonical forms are equal. -/
def alphaEquivalent (left right : Json) : Except String Bool := do
  let leftForm ← alphaNormalize left
  let rightForm ← alphaNormalize right
  return leftForm == rightForm

end ExprGraphV2

