/-
  GoalGraphCore: self-contained goal-aware ExprGraph builder.

  This module intentionally has no `main`, so exporter executables can import
  it.  `Standalone/ExprGraphExport.lean` contains the same graph primitives for
  its statement CLI; the goal-aware functions here are kept behaviourally
  identical (see experiments/exprgraph/test_goal_graph.py).
-/
import Nazrin.Essentialization
import Lean.Data.Json

open Lean

namespace GoalGraphCore

/-! ## Small formatting helpers -/

/-- Canonical string for a universe level.  This is a stable, human-readable
encoding used as a node feature; it is not meant to round-trip through Lean. -/
partial def levelToString : Level → String
  | .zero => "0"
  | .succ u => s!"(succ {levelToString u})"
  | .max u v => s!"(max {levelToString u} {levelToString v})"
  | .imax u v => s!"(imax {levelToString u} {levelToString v})"
  | .param n => n.toString
  | .mvar m => s!"?{m.name}"

/-- Ground universe levels as natural numbers, when possible. -/
partial def levelToNat? : Level → Option Nat
  | .zero => some 0
  | .succ u => (levelToNat? u).map (· + 1)
  | _ => none

/-- A `Sort` is `Prop`, `Type n`, or a non-ground `Sort u`. -/
def sortToString (u : Level) : String :=
  match u with
  | .zero => "Prop"
  | .succ v =>
    match levelToNat? v with
    | some 0 => "Type"
    | some n => s!"Type {n}"
    | none => s!"Sort {levelToString u}"
  | _ => s!"Sort {levelToString u}"

/-- Dot-separated `SubExpr.Pos`, with the root represented by the empty string.
This is the position format required by the JSON schema (e.g. `0.1.0`). -/
def posToPath (p : SubExpr.Pos) : String :=
  String.intercalate "." (p.toArray.toList.map toString)

def litKey : Literal → String
  | .natVal n => s!"nat:{n}"
  | .strVal s => s!"str:{s}"

def litValue : Literal → String
  | .natVal n => toString n
  | .strVal s => s

def litType : Literal → String
  | .natVal _ => "nat"
  | .strVal _ => "string"

/-! ## Graph construction state -/

/-- Mutable state of one graph build.  Node ids are array indices, hence
contiguous by construction.  `consts`, `sorts`, `lits`, `fvars`, and `mvars`
implement condensation: the first occurrence creates a shared node and later
occurrences reuse it. -/
structure GraphState where
  nodes : Array Json := #[]
  edges : Array Json := #[]
  loci : Array Json := #[]
  consts : Std.HashMap Name Nat := {}
  constList : Array (Name × Nat) := #[]
  sorts : Std.HashMap String Nat := {}
  lits : Std.HashMap String Nat := {}
  fvars : Std.HashMap FVarId Nat := {}
  fvarList : Array (FVarId × Nat) := #[]
  mvars : Std.HashMap MVarId Nat := {}
  mvarList : Array (MVarId × Nat) := #[]
  /-- Every node position ever emitted.  Used by the goal-aware exporter to
  allocate distinct positions for metadata-only subgraphs. -/
  usedPositions : Std.HashSet String := {}
  /-- When false, `addLocus` is a no-op.  Statement graphs always keep this
  true; fvar type/value subgraphs are metadata and must not pollute the goal's
  rewritable-locus table. -/
  trackLoci : Bool := true

abbrev BuildM := StateM GraphState

def mkNode (id : Nat) (kind : String) (position : String) (depth : Nat)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj <|
    [("id", toJson id), ("kind", toJson kind)] ++
    extra ++
    [("position", toJson position), ("depth", toJson depth)]

def addNode (kind : String) (position : String) (depth : Nat)
    (extra : List (String × Json) := []) : BuildM Nat := do
  let id := (← get).nodes.size
  modify fun s => { s with
    nodes := s.nodes.push (mkNode id kind position depth extra)
    usedPositions := s.usedPositions.insert position }
  return id

def addEdge (src dst : Nat) (edgeType : String) : BuildM Unit :=
  modify fun s =>
    { s with edges := s.edges.push <| Json.mkObj [
        ("src", toJson src), ("dst", toJson dst), ("type", toJson edgeType)] }

/-- Record a rewrite locus.  The same position is never recorded twice; the
node may be shared (constants/sorts/literals) because of condensation. -/
def addLocus (position : SubExpr.Pos) (node : Nat) : BuildM Unit := do
  unless (← get).trackLoci do return
  modify fun s =>
    { s with loci := s.loci.push <| Json.mkObj [
        ("position", toJson (posToPath position)), ("node", toJson node)] }

def getOrCreateConst (name : Name) (levels : List Level)
    (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  let s ← get
  match s.consts[name]? with
  | some id => return id
  | none =>
    let id := s.nodes.size
    let jsonLevels : Array Json :=
      (levels.map fun u => toJson (levelToString u)).toArray
    let node := mkNode id "const" (posToPath position) depth [
      ("const", toJson name.toString), ("level", Json.arr jsonLevels)]
    set { s with
      nodes := s.nodes.push node
      consts := s.consts.insert name id
      constList := s.constList.push (name, id)
      usedPositions := s.usedPositions.insert (posToPath position) }
    return id

def getOrCreateSort (level : Level) (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  let s ← get
  let key := sortToString level
  match s.sorts[key]? with
  | some id => return id
  | none =>
    let id := s.nodes.size
    let node := mkNode id "sort" (posToPath position) depth [("sort", toJson key)]
    set { s with
      nodes := s.nodes.push node
      sorts := s.sorts.insert key id
      usedPositions := s.usedPositions.insert (posToPath position) }
    return id

def getOrCreateLit (value : Literal) (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  let s ← get
  let key := litKey value
  match s.lits[key]? with
  | some id => return id
  | none =>
    let id := s.nodes.size
    let node := mkNode id "lit" (posToPath position) depth [
      ("lit", toJson (litValue value)), ("litType", toJson (litType value))]
    set { s with
      nodes := s.nodes.push node
      lits := s.lits.insert key id
      usedPositions := s.usedPositions.insert (posToPath position) }
    return id

def getOrCreateFVar (id : FVarId) (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  let s ← get
  match s.fvars[id]? with
  | some node => return node
  | none =>
    let index := s.fvarList.size
    let node ← addNode "fvar" (posToPath position) depth [("fvar", toJson index)]
    modify fun s => { s with
      fvars := s.fvars.insert id node
      fvarList := s.fvarList.push (id, node) }
    return node

def getOrCreateMVar (id : MVarId) (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  let s ← get
  match s.mvars[id]? with
  | some node => return node
  | none =>
    let index := s.mvarList.size
    let node ← addNode "mvar" (posToPath position) depth [("mvar", toJson index)]
    modify fun s => { s with
      mvars := s.mvars.insert id node
      mvarList := s.mvarList.push (id, node) }
    return node

/-- Build the graph of `e`.  `mdata` is erased (it is a presentation wrapper,
and `SubExpr.Pos` is transparent to it), which keeps alpha-equivalent and
search-view-equivalent terms closer together. -/
partial def buildExpr (e : Expr) (position : SubExpr.Pos) (depth : Nat) : BuildM Nat := do
  match e with
  | .mdata _ inner => buildExpr inner position depth
  | .const name levels => getOrCreateConst name levels position depth
  | .sort level => getOrCreateSort level position depth
  | .lit value => getOrCreateLit value position depth
  | .fvar id => getOrCreateFVar id position depth
  | .mvar id => getOrCreateMVar id position depth
  | .bvar index =>
    addNode "bvar" (posToPath position) depth [("bvar", toJson index)]
  | .app fn arg =>
    let node ← addNode "app" (posToPath position) depth
    let fnNode ← buildExpr fn position.pushAppFn (depth + 1)
    addEdge node fnNode "app_fn"
    addLocus position.pushAppFn fnNode
    let argNode ← buildExpr arg position.pushAppArg (depth + 1)
    addEdge node argNode "app_arg"
    addLocus position.pushAppArg argNode
    return node
  | .lam _ type body _ =>
    let node ← addNode "lam" (posToPath position) depth
    let typeNode ← buildExpr type position.pushBindingDomain (depth + 1)
    addEdge node typeNode "binder_type"
    addLocus position.pushBindingDomain typeNode
    let bodyNode ← buildExpr body position.pushBindingBody (depth + 1)
    addEdge node bodyNode "binder_body"
    addLocus position.pushBindingBody bodyNode
    return node
  | .forallE _ type body _ =>
    let node ← addNode "forallE" (posToPath position) depth
    let typeNode ← buildExpr type position.pushBindingDomain (depth + 1)
    addEdge node typeNode "binder_type"
    addLocus position.pushBindingDomain typeNode
    let bodyNode ← buildExpr body position.pushBindingBody (depth + 1)
    addEdge node bodyNode "binder_body"
    addLocus position.pushBindingBody bodyNode
    return node
  | .letE _ type value body _ =>
    let node ← addNode "letE" (posToPath position) depth
    let typeNode ← buildExpr type position.pushLetVarType (depth + 1)
    addEdge node typeNode "let_type"
    addLocus position.pushLetVarType typeNode
    let valueNode ← buildExpr value position.pushLetValue (depth + 1)
    addEdge node valueNode "let_value"
    addLocus position.pushLetValue valueNode
    let bodyNode ← buildExpr body position.pushLetBody (depth + 1)
    addEdge node bodyNode "let_body"
    addLocus position.pushLetBody bodyNode
    return node
  | .proj structName fieldIndex inner =>
    let node ← addNode "proj" (posToPath position) depth [
      ("projStruct", toJson structName.toString), ("projField", toJson fieldIndex)]
    let structNode ← buildExpr inner position.pushProj (depth + 1)
    addEdge node structNode "proj_struct"
    addLocus position.pushProj structNode
    return node

/-- Build one complete graph from a closed theorem type. -/
def buildGraph (type : Expr) : GraphState × Nat :=
  let (root, state) := (do
    let root ← buildExpr type .root 0
    addLocus .root root
    return root).run {}
  (state, root)

/-! ## JSON serialisation -/

def graphToJson (theoremName : Name) (moduleName : String)
    (state : GraphState) (root : Nat) : Json :=
  let fvarJson := state.fvarList.mapIdx fun index (id, node) =>
    Json.mkObj [
      ("index", toJson index),
      ("name", toJson id.name.toString),
      ("node", toJson node),
      ("type_node", Json.null)]
  let mvarJson := state.mvarList.mapIdx fun index (id, node) =>
    Json.mkObj [
      ("index", toJson index),
      ("name", toJson id.name.toString),
      ("node", toJson node)]
  let constJson := state.constList.map fun (name, node) =>
    Json.mkObj [("name", toJson name.toString), ("node", toJson node)]
  Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("theorem", toJson theoremName.toString),
    ("module", toJson moduleName),
    ("root", toJson root),
    ("nodes", Json.arr state.nodes),
    ("edges", Json.arr state.edges),
    ("loci", Json.arr state.loci),
    ("fvars", Json.arr fvarJson),
    ("constants", Json.arr constJson),
    ("mvars", Json.arr mvarJson)]

/-! ## Goal-aware graphs

The statement exporter above is intentionally closed-term only.  The functions
below add proof-state graphs without changing any statement output: `fvars`
gain real `type_node` (and, for let-declarations, `value_node`) entries, and
the root is the instantiated goal target rather than the first local
declaration.

Metadata-only subgraphs (fvar types and let values) do not participate in the
goal's rewritable-locus table.  Their node positions are allocated in a fresh
synthetic branch so that they remain unique and deterministic. -/

/-- A local declaration prepared for graph construction.  `value?` is present
for both dependent and non-dependent let-declarations; `nondep` records the
latter, whose value Lean documents as potentially type-incorrect. -/
structure GoalLocal where
  fvarId : FVarId
  name : Name
  type : Expr
  value? : Option Expr := none
  isLet : Bool := false
  nondep : Bool := false
  /-- Unique display name; duplicates in a local context receive `#0`, `#1`, … -/
  displayName : String := ""

structure GoalFVarInfo where
  fvarId : FVarId
  name : String
  typeNode : Nat
  valueNode? : Option Nat := none

/-- Deterministic unique display names for a local context.  Lean permits
duplicate user names (e.g. several `x` hypotheses); `fvars[].name` must be
unique so downstream candidate pointers are unambiguous.  The first occurrence
keeps the user name, later occurrences get `name#1`, `name#2`, … -/
def localDisplayNames (lctx : LocalContext) : Std.HashMap FVarId String := Id.run do
  let mut usedNames : Std.HashSet String := {}
  let mut nextSuffix : Std.HashMap String Nat := {}
  let mut names : Std.HashMap FVarId String := {}
  for ldecl in lctx do
    let base := ldecl.userName.toString
    let mut display := base
    if usedNames.contains display then
      let mut index := nextSuffix.getD base 1
      display := s!"{base}#{index}"
      while usedNames.contains display do
        index := index + 1
        display := s!"{base}#{index}"
      nextSuffix := nextSuffix.insert base (index + 1)
    usedNames := usedNames.insert display
    names := names.insert ldecl.fvarId display
  return names

structure GoalGraphBuild where
  state : GraphState
  root : Nat
  fvars : Array GoalFVarInfo
  warnings : Array String := #[]

/-- True when `prefix` is already used by a node or is an ancestor of a used
node position. -/
def positionPrefixUsed (s : GraphState) (pre : String) : Bool :=
  s.usedPositions.toList.any fun p =>
    p == pre || p.startsWith (pre ++ ".")

/-- Allocate a deterministic, currently unused position branch.  `3` is never
a child coordinate of `app` (0/1), `forallE` (0/1), `letE` (0/1/2), or `proj`
(0), so the first candidate is normally free.  Deeper candidates only occur
when several metadata subgraphs are emitted in sequence. -/
partial def freshMetadataPos (s : GraphState) : SubExpr.Pos :=
  let rec go (coords : Array Nat) (fuel : Nat) : SubExpr.Pos :=
    let p := SubExpr.Pos.ofArray coords
    if fuel == 0 || !positionPrefixUsed s (posToPath p) then p
    else go (coords.push 3) (fuel - 1)
  go #[3] 256

/-- Pure construction of a goal graph from an already-instantiated target and
prepared local declarations. -/
def buildGoalGraphState (target : Expr) (locals : Array GoalLocal) : GoalGraphBuild :=
  Id.run do
    let (root, s0) := (do
      let root ← buildExpr target .root 0
      addLocus .root root
      return root).run {}
    let mut state := s0
    let mut infos : Array GoalFVarInfo := #[]
    let mut warnings : Array String := #[]
    for loc in locals do
      let fvarPos := freshMetadataPos state
      let (node, s1) := (getOrCreateFVar loc.fvarId fvarPos 0).run state
      state := s1
      let typePos := freshMetadataPos state
      let (typeNode, s2) :=
        (buildExpr loc.type typePos 0).run { state with trackLoci := false }
      state := { s2 with trackLoci := true }
      let (_, s3) := (addEdge node typeNode "fvar_type").run state
      state := s3
      if loc.nondep then
        warnings := warnings.push
          s!"local declaration {loc.name} is a non-dependent let; its value is opaque and may be type-incorrect"
      let mut valueNode? : Option Nat := none
      if let some value := loc.value? then
        let valuePos := freshMetadataPos state
        let (vn, s4) :=
          (buildExpr value valuePos 0).run { state with trackLoci := false }
        state := { s4 with trackLoci := true }
        let (_, s5) := (addEdge node vn "fvar_value").run state
        state := s5
        valueNode? := some vn
      infos := infos.push {
        fvarId := loc.fvarId
        name := if loc.displayName.isEmpty then loc.name.toString else loc.displayName
        typeNode := typeNode
        valueNode? := valueNode?
      }
    return { state := state, root := root, fvars := infos, warnings := warnings }

/-- Serialise a goal graph.  This is schema v1 plus:
* `goal_id` (the metavariable name),
* `fvars[].index/name/node/type_node` (and optional `value_node`),
* `parse_warnings`.

The statement exporter's `graphToJson` is deliberately left untouched, so old
statement JSONL stays byte-compatible. -/
def goalGraphToJson (goalId : String) (build : GoalGraphBuild) : Json :=
  let fvarJson := build.state.fvarList.mapIdx fun index (id, node) =>
    let info? := build.fvars.find? fun info => info.fvarId == id
    let name := info?.map (fun info => info.name) |>.getD id.name.toString
    let typeNode : Json :=
      match info? with
      | some info => toJson info.typeNode
      | none => Json.null
    let valueField : List (String × Json) :=
      match info?.bind (fun info => info.valueNode?) with
      | some vn => [("value_node", toJson vn)]
      | none => []
    Json.mkObj <|
      [("index", toJson index),
       ("name", toJson name),
       ("node", toJson node),
       ("type_node", typeNode)] ++ valueField
  let mvarJson := build.state.mvarList.mapIdx fun index (id, node) =>
    Json.mkObj [
      ("index", toJson index),
      ("name", toJson id.name.toString),
      ("node", toJson node)]
  let constJson := build.state.constList.map fun (name, node) =>
    Json.mkObj [("name", toJson name.toString), ("node", toJson node)]
  Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("goal_id", toJson goalId),
    ("root", toJson build.root),
    ("nodes", Json.arr build.state.nodes),
    ("edges", Json.arr build.state.edges),
    ("loci", Json.arr build.state.loci),
    ("fvars", Json.arr fvarJson),
    ("constants", Json.arr constJson),
    ("mvars", Json.arr mvarJson),
    ("parse_warnings", Json.arr (build.warnings.map toJson))]

/-- `instantiateAll` with a warning fallback: a raw expression with metavariables
is still exportable and is never silently replaced by a different term. -/
def instantiateForGraph (e : Expr) (label : String) : MetaM (Expr × Array String) := do
  try
    let e' ← Nazrin.instantiateAll e
    let mut warnings : Array String := #[]
    if e'.hasExprMVar then
      warnings := warnings.push s!"{label}: metavariables remain after instantiateAll"
    return (e', warnings)
  catch ex =>
    let message ← ex.toMessageData.toString
    return (e, #[s!"{label}: instantiateAll failed ({message}); using raw expression"])

/-- Build the goal-aware graph of `mvarId` under an explicit goal id, also
returning the accumulated warnings. -/
def buildGoalGraphAsFull (mvarId : MVarId) (goalId : String) : MetaM (Json × Array String) := do
  let decl ← mvarId.getDecl
  let (target, targetWarnings) ← instantiateForGraph (← mvarId.getType) "target"
  let mut locals : Array GoalLocal := #[]
  let mut warnings := targetWarnings
  for ldecl in decl.lctx do
    let (type, typeWarnings) ← instantiateForGraph ldecl.type s!"local {ldecl.userName}"
    warnings := warnings ++ typeWarnings
    let value? ← match ldecl.value? with
      | none => pure none
      | some value =>
        let (value, valueWarnings) ← instantiateForGraph value s!"local {ldecl.userName} value"
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
        | .cdecl .. => false
    }
  let displayNames := localDisplayNames decl.lctx
  locals := locals.map fun loc => { loc with displayName := displayNames[loc.fvarId]?.getD loc.name.toString }
  let build := buildGoalGraphState target locals
  let allWarnings := warnings ++ build.warnings
  return (goalGraphToJson goalId { build with warnings := allWarnings }, allWarnings)

/-- Build the goal-aware graph of `mvarId` under an explicit goal id. -/
def buildGoalGraphAs (mvarId : MVarId) (goalId : String) : MetaM Json := do
  return (← buildGoalGraphAsFull mvarId goalId).1

/-- Build the goal-aware graph of `mvarId`; the goal id defaults to the
metavariable's own name. -/
def buildGoalGraph (mvarId : MVarId) : MetaM Json :=
  buildGoalGraphAs mvarId mvarId.name.toString

/-- Goal graph with theorem/module provenance attached. -/
def buildGoalGraphJson (theoremName : Name) (moduleName : String) (mvarId : MVarId) : MetaM Json := do
  let graph ← buildGoalGraph mvarId
  let graph := graph.setObjVal! "theorem" (toJson theoremName.toString)
  return graph.setObjVal! "module" (toJson moduleName)


end GoalGraphCore
