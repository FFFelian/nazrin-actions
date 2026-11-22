/-
  ExprGraphV3: schema-3 ExprGraph with cross-goal goal edges, global constant
  identity, and an explicit best-effort search-view normalizer.

  This is a **library module**: no `main`.  It imports the untouched v2 module
  and upgrades its schema-2 output.  It does not change v1/v2, the model,
  training, or search.  The contract is documented in
  `experiments/exprgraph/v3/schema-v3.md`.

  Important boundary: the paper does not publish the authors' code, and its
  prose does not pin down every reduction/expansion choice.  This module is a
  best-effort executable specification, not a claim of bit-for-bit identity
  with an unavailable implementation.  Every non-definitional choice is named
  in comments and in the schema document.

  v3 additions over v2:
  * schema 3 wire format (`coupled` becomes an object with `goal_edges` and
    `groups`);
  * `goal_edges`: shared-fvar edges plus edges induced by a goal target that
    mentions another goal's fvar/mvar;
  * `constants[].global_id` and `nodes[].global_id`, computed by a stable
    cross-graph content hash of the constant name;
  * `searchViewNormalizeV3`: mdata erasure, binder-info reset, zeta, beta,
    eta-reduction, universe-parameter alpha-renaming, and name normalization;
  * `alphaNormalizeV3`: schema-3 canonical form used for alpha comparisons;
  * `essentializeV3` / `essentializeV3Detailed`: the v1 instantiation pipeline
    with a before/after record and warnings.
-/
import Standalone.ExprGraphV2
import Lean.Data.Json

open Lean

namespace ExprGraphV3

/-! ## Small JSON helpers (same non-throwing style as v2) -/

def jsonStrD (j : Json) (key : String) (default : String := "") : String :=
  match j.getObjValD key with
  | .null => default
  | v => (v.getStr?).toOption.getD default

def jsonNatD (j : Json) (key : String) (default : Nat := 0) : Nat :=
  match j.getObjValD key with
  | .null => default
  | v => (v.getNat?).toOption.getD default

def jsonAsNatD (j : Json) (default : Nat := 0) : Nat :=
  (j.getNat?).toOption.getD default

def arrFieldD (j : Json) (key : String) : Array Json :=
  match j.getObjValD key with
  | .null => #[]
  | v => (v.getArr?).toOption.getD #[]

def schemaVersion : Nat := 3

/-! ## Global constant identity

The paper's condensation property is naturally graph-global, but schema 2 only
had a per-graph `constants` table.  Schema 3 attaches a stable id derived from
the fully qualified constant name.  We use FNV-1a 64-bit over the UTF-8 bytes
and print the 16 hexadecimal digits.  This is deliberately **not** a
cryptographic hash and carries no security promise; it is only a stable
cross-file identity.  Collisions are possible in principle (64 bits); the
validator rejects duplicate ids *within one graph* and tests cross-graph
consistency for known names.
-/

private def fnvOffset : UInt64 := 14695981039346656037
private def fnvPrime : UInt64 := 1099511628211

private def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * fnvPrime) fnvOffset

private def hexDigit (n : Nat) : Char :=
  match n with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

private def hexDigits (fuel v : Nat) (acc : List Char) : List Char :=
  match fuel with
  | 0 => acc
  | n + 1 => hexDigits n (v / 16) (hexDigit (v % 16) :: acc)

/-- Stable, 16-hex-digit identity of a constant name.  The same name yields the
same string in every graph and every process.  This is an identity, not a
security hash. -/
def globalConstantId (name : Name) : String :=
  String.ofList (hexDigits 16 (fnv1a64 name.toString).toNat [])

/-! ## Target references used by goal edges -/

/-- A pair of goals plus the fvar indices that justify the edge.  An edge with
an empty fvar list still counts: it is created by a target that mentions the
other goal's metavariable.  `mvars` are not serialized in schema 3 (the required
`goal_edges` object is `src`/`dst`/`fvars`); the edge itself is the record. -/
structure TargetRelations where
  fvarPairs : Array (Nat × Nat × Nat) := #[]
  mvarPairs : Array (Nat × Nat) := #[]
  warnings : Array String := #[]

/-- One goal's reference-relevant view. -/
structure GoalReferenceInfo where
  goalId : String
  mvarId : MVarId
  target : Expr
  locals : Array FVarId := #[]
deriving Inhabited

partial def collectExprFVars (e : Expr) (acc : Std.HashSet FVarId) : Std.HashSet FVarId :=
  match e with
  | .fvar id => acc.insert id
  | .app fn arg => collectExprFVars arg (collectExprFVars fn acc)
  | .lam _ type body _ => collectExprFVars body (collectExprFVars type acc)
  | .forallE _ type body _ => collectExprFVars body (collectExprFVars type acc)
  | .letE _ type value body _ =>
      collectExprFVars body (collectExprFVars value (collectExprFVars type acc))
  | .proj _ _ inner => collectExprFVars inner acc
  | .mdata _ inner => collectExprFVars inner acc
  | _ => acc

partial def collectExprMVars (e : Expr) (acc : Std.HashSet MVarId) : Std.HashSet MVarId :=
  match e with
  | .mvar id => acc.insert id
  | .app fn arg => collectExprMVars arg (collectExprMVars fn acc)
  | .lam _ type body _ => collectExprMVars body (collectExprMVars type acc)
  | .forallE _ type body _ => collectExprMVars body (collectExprMVars type acc)
  | .letE _ type value body _ =>
      collectExprMVars body (collectExprMVars value (collectExprMVars type acc))
  | .proj _ _ inner => collectExprMVars inner acc
  | .mdata _ inner => collectExprMVars inner acc
  | _ => acc

/-- Prepare the raw reference information before calling the v2 builder.  The
target is instantiated so assigned metavariables do not hide a cross-goal
reference.  Failures become warnings and an empty reference set; the v2
builder's own warnings are still returned by the public entry point. -/
def prepareGoalReferences (goals : Array (String × MVarId)) :
    MetaM (Array GoalReferenceInfo × Array String) := do
  let mut infos : Array GoalReferenceInfo := #[]
  let mut warnings : Array String := #[]
  for (goalId, mvarId) in goals do
    try
      let decl ← mvarId.getDecl
      let target ← instantiateMVars (← mvarId.getType)
      let mut locals : Array FVarId := #[]
      for ldecl in decl.lctx do
        locals := locals.push ldecl.fvarId
      infos := infos.push { goalId := goalId, mvarId := mvarId, target := target, locals := locals }
    catch ex =>
      let message ← ex.toMessageData.toString
      warnings := warnings.push s!"v3 goal edge: could not inspect {goalId}: {message}"
  return (infos, warnings)

/-- Compute cross-goal target references.  `fvarPairs` has one entry per
`(target goal, declaring goal, fvar index)`; `mvarPairs` has one entry per
`(target goal, goal owning the mentioned mvar)`.  Self references are ignored,
as are target fvars declared by no exported goal. -/
def targetRelations (infos : Array GoalReferenceInfo) : TargetRelations := Id.run do
  let mut indexByMVar : Std.HashMap MVarId Nat := {}
  let mut declaredBy : Std.HashMap FVarId (Array Nat) := {}
  for i in [:infos.size] do
    indexByMVar := indexByMVar.insert infos[i]!.mvarId i
    for fvarId in infos[i]!.locals do
      declaredBy := declaredBy.insert fvarId ((declaredBy.getD fvarId #[]).push i)
  -- Recreate the v2 fvar table order: first declaration in goal order.
  let mut fvarIndex : Std.HashMap FVarId Nat := {}
  let mut nextIndex := 0
  for info in infos do
    for fvarId in info.locals do
      unless fvarIndex.contains fvarId do
        fvarIndex := fvarIndex.insert fvarId nextIndex
        nextIndex := nextIndex + 1
  let mut fvarPairs : Array (Nat × Nat × Nat) := #[]
  let mut mvarPairs : Array (Nat × Nat) := #[]
  for i in [:infos.size] do
    let info := infos[i]!
    let targetFVars := (collectExprFVars info.target {}).toList
    for fvarId in targetFVars do
      if let some idx := fvarIndex[fvarId]? then
        for j in declaredBy.getD fvarId #[] do
          if j != i then
            fvarPairs := fvarPairs.push (i, j, idx)
    let targetMVars := (collectExprMVars info.target {}).toList
    for mvarId in targetMVars do
      if let some j := indexByMVar[mvarId]? then
        if j != i then
          mvarPairs := mvarPairs.push (i, j)
  return { fvarPairs := fvarPairs, mvarPairs := mvarPairs }

/-! ## Coupled goal graph -/

def sortUnique (xs : Array Nat) : Array Nat := Id.run do
  let sorted := xs.qsort (· < ·)
  let mut out : Array Nat := #[]
  for x in sorted do
    if out.isEmpty || out.back! != x then
      out := out.push x
  return out

def pairKey (a b : Nat) : Nat × Nat := (if a < b then a else b, if a < b then b else a)

def insertFvarEdge (m : Std.HashMap (Nat × Nat) (Array Nat)) (a b fvar : Nat) :
    Std.HashMap (Nat × Nat) (Array Nat) :=
  let key := pairKey a b
  let old := m.getD key #[]
  m.insert key (old.push fvar)

def insertEmptyEdge (m : Std.HashMap (Nat × Nat) (Array Nat)) (a b : Nat) :
    Std.HashMap (Nat × Nat) (Array Nat) :=
  let key := pairKey a b
  m.insert key (m.getD key #[])

/-- Build the schema-3 `coupled` object.

`goal_edges` is the union of:
* all pairs of goals that declare the same fvar (with that fvar index), and
* target references to another goal's fvar/mvar (mvar-only edges have `fvars`).

`groups` is the connected-component decomposition of **goal_edges**, sorted by
goal order.  A group's `fvars` is the sorted union of fvar indices carried by
the edges inside that component.  This deliberately generalizes v2's
shared-fvar-only groups: a pair linked only through a target metavariable is
still a coupled edge/group in v3. -/
def buildCoupledV3 (graph : Json) (extra : TargetRelations := {}) : Json := Id.run do
  let goals := arrFieldD graph "goals"
  let goalIds : Array String := goals.map fun g => jsonStrD g "goal_id" ""
  let n := goals.size
  let mut goalIndex : Std.HashMap String Nat := {}
  for i in [:n] do
    goalIndex := goalIndex.insert goalIds[i]! i
  let mut edges : Std.HashMap (Nat × Nat) (Array Nat) := {}
  -- Shared-fvar relation from the v2 fvar table.
  for fv in arrFieldD graph "fvars" do
    let fvarIndex := jsonNatD fv "index"
    let declGoals := (arrFieldD fv "goals").filterMap fun g =>
      goalIndex[(g.getStr?).toOption.getD ""]?
    for a in declGoals do
      for b in declGoals do
        if a < b then
          edges := insertFvarEdge edges a b fvarIndex
  for (a, b, fvarIndex) in extra.fvarPairs do
    if a < n && b < n && a != b then
      edges := insertFvarEdge edges a b fvarIndex
  for (a, b) in extra.mvarPairs do
    if a < n && b < n && a != b then
      edges := insertEmptyEdge edges a b
  let edgeList : Array (Nat × Nat × Array Nat) :=
    (edges.toList.map fun ((a, b), fvars) => (a, b, sortUnique fvars)).toArray
      |>.qsort fun (a1, b1, _) (a2, b2, _) =>
        a1 < a2 || (a1 == a2 && b1 < b2)
  -- Undirected adjacency for connected components.
  let mut adjacency : Array (Array Nat) := Array.replicate n #[]
  for (a, b, _) in edgeList do
    adjacency := adjacency.set! a ((adjacency[a]!).push b)
    adjacency := adjacency.set! b ((adjacency[b]!).push a)
  let mut visited : Array Bool := Array.replicate n false
  let mut groups : Array Json := #[]
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
        let mut groupFVars : Array Nat := #[]
        for (a, b, fvars) in edgeList do
          if sortedComponent.contains a && sortedComponent.contains b then
            groupFVars := groupFVars ++ fvars
        groups := groups.push <| Json.mkObj [
          ("goals", Json.arr (sortedComponent.map fun i => Lean.toJson goalIds[i]!)),
          ("fvars", Json.arr ((sortUnique groupFVars).map Lean.toJson))]
  let goalEdges := edgeList.map fun (a, b, fvars) =>
    Json.mkObj [
      ("src", Lean.toJson goalIds[a]!),
      ("dst", Lean.toJson goalIds[b]!),
      ("fvars", Json.arr (fvars.map Lean.toJson))]
  return Json.mkObj [
    ("goal_edges", Json.arr goalEdges),
    ("groups", Json.arr groups)]

/-- Attach constant ids to nodes and the constants table, bump the schema, and
rewrite `coupled` to the v3 object. -/
def upgradeGraphToV3 (graph : Json) (extra : TargetRelations := {}) : Json :=
  let nodes := (arrFieldD graph "nodes").map fun node =>
    if jsonStrD node "kind" == "const" then
      let name := jsonStrD node "const" ""
      node.setObjVal! "global_id" (Lean.toJson (globalConstantId name.toName))
    else node
  let constants := (arrFieldD graph "constants").map fun entry =>
    let name := jsonStrD entry "name" ""
    Json.mkObj [
      ("name", Lean.toJson name),
      ("global_id", Lean.toJson (globalConstantId name.toName)),
      ("node", Lean.toJson (jsonNatD entry "node" 0))]
  let graph := graph.setObjVal! "schema" (Lean.toJson schemaVersion)
  let graph := graph.setObjVal! "nodes" (Json.arr nodes)
  let graph := graph.setObjVal! "constants" (Json.arr constants)
  graph.setObjVal! "coupled" (buildCoupledV3 graph extra)

/-! ## Goal-state and constant-graph entry points -/

/-- Schema-3 proof-state graph with explicit goal ids and provenance.  This
calls the untouched v2 builder, then upgrades and enriches it. -/
def buildGoalStateGraphNamedFullV3 (theoremName : String) (moduleName : Option String)
    (goals : Array (String × MVarId)) : MetaM (Json × Array String) := do
  let ids := ExprGraphV2.uniqueGoalIds (goals.map fun (id, _) => id)
  let goals := goals.zip ids |>.map fun ((_, mvarId), id) => (id, mvarId)
  let (infos, referenceWarnings) ← prepareGoalReferences goals
  let extra :=
    if infos.size == goals.size then targetRelations infos
    else { warnings := #["v3 goal edge: goal inspection incomplete; no target-reference edges emitted"] }
  let (graph, warnings) ←
    ExprGraphV2.buildGoalStateGraphNamedFull theoremName moduleName goals
  let graph := upgradeGraphToV3 graph extra
  return (graph, warnings ++ referenceWarnings ++ extra.warnings)

/-- Schema-3 coupled-goal entry point.  Goal ids default to metavariable names;
`theorem` is empty because no provenance was supplied. -/
def buildGoalStateGraphV3 (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFullV3 "" none pairs).1

def buildGoalStateGraphAsV3 (theoremName : Name) (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFullV3 theoremName.toString none pairs).1

def buildGoalStateGraphJsonV3 (theoremName : Name) (moduleName : String)
    (goals : List MVarId) : MetaM Json := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return (← buildGoalStateGraphNamedFullV3 theoremName.toString (some moduleName) pairs).1

def buildGoalStateGraphFullV3 (theoremName : Name) (goals : List MVarId) :
    MetaM (Json × Array String) := do
  let pairs : Array (String × MVarId) :=
    goals.toArray.map fun mvarId => (mvarId.name.toString, mvarId)
  return ← buildGoalStateGraphNamedFullV3 theoremName.toString none pairs

/-- Schema-3 constant graph: type plus value when enabled, with global ids on
both the `const` nodes and the `constants` table.  Unknown/failed constants
return `none` with a warning, matching v2. -/
def buildConstantGraphWithV3 (cfg : ExprGraphV2.ConstantGraphConfig) (name : Name) :
    MetaM (Option Json × Array String) := do
  let (graph?, warnings) ← ExprGraphV2.buildConstantGraphWith cfg name
  match graph? with
  | none => return (none, warnings)
  | some graph => return (some (upgradeGraphToV3 graph), warnings)

def buildConstantGraphV3Full (name : Name) : MetaM (Option Json × Array String) :=
  buildConstantGraphWithV3 {} name

def buildConstantGraphV3 (name : Name) : MetaM (Option Json) :=
  return (← buildConstantGraphV3Full name).1

/-! ## Essentialization with a before/after record -/

/-- Result of `essentializeV3Detailed`.  `before`/`after` are the actual
expressions; `changed` compares them structurally. -/
structure EssentializeV3Result where
  before : Expr
  after : Expr
  changed : Bool
  warnings : Array String := #[]

/-- Essentialize with the untouched v1/v2 pipeline (`Nazrin.instantiateAll`).
A failure keeps the raw expression and must carry a warning. -/
def essentializeV3Detailed (e : Expr) (label : String := "expression") :
    MetaM EssentializeV3Result := do
  let (after, warnings) ← ExprGraphV2.essentialize e label
  return { before := e, after := after, changed := e != after, warnings := warnings }

def essentializeV3 (e : Expr) (label : String := "expression") :
    MetaM (Expr × Array String) := do
  let result ← essentializeV3Detailed e label
  return (result.after, result.warnings)

/-! ## Search-view normalization (best-effort executable specification)

The transformations below are intentionally explicit.  They are a *chosen*
normal form, not a decision procedure for Lean definitional equality and not a
reconstruction of the unavailable author implementation.

1. `mdata` wrappers are erased (presentation only).
2. Binder info is reset to `BinderInfo.default`; binder names are canonicalized.
3. `letE` is zeta-reduced unconditionally.
4. Beta-redexes introduced by zeta or present originally are reduced.
5. Eta is **reduced**, never expanded: `fun x => f x` becomes `f` when `x` does
   not occur in `f`.  This is the shorter direction and needs no type inference.
6. Universe parameters are alpha-renamed by first occurrence to `u0`, `u1`, ...
   (both in `const` level arguments and in sorts).
7. Free variables are preserved by default.  `alphaNormalizeExprV3` optionally
   renames them to `fv0`, ... for standalone alpha comparisons; the graph
   canonicalizer always renumbers fvar nodes, so search-view graphs do not need
   expression-level fvar renaming (which would break local-context linkage).
8. Delayed metavariables are **preserved** and reported in warnings.
9. Projections are **preserved structurally** (the `.proj` node remains).
   Recursors and definitions are **preserved** as constants, except that the
   essentialization pass may unfold the internal/auxiliary definitions that
   `Nazrin.instantiateAll` already unfolds.  Failures of that pass are warnings.
-/

structure AlphaExprOptions where
  canonicalizeBinderNames : Bool := true
  canonicalizeUniverses : Bool := true
  canonicalizeFVars : Bool := false

structure AlphaExprState where
  binderCounter : Nat := 0
  universeCounter : Nat := 0
  fvarCounter : Nat := 0
  universes : Std.HashMap Name Nat := {}
  fvars : Std.HashMap FVarId FVarId := {}
  warned : Std.HashSet String := {}

private def canonicalBinderName (st : AlphaExprState) : Name × AlphaExprState :=
  (Name.mkSimple s!"x{st.binderCounter}", { st with binderCounter := st.binderCounter + 1 })

private def warnOnce (st : AlphaExprState) (message : String) :
    AlphaExprState × Array String :=
  if st.warned.contains message then (st, #[])
  else ({ st with warned := st.warned.insert message }, #[message])

partial def alphaLevel (opts : AlphaExprOptions) (st : AlphaExprState) (l : Level) :
    Level × AlphaExprState × Array String :=
  match l with
  | .zero => (.zero, st, #[])
  | .succ u =>
      let (u', st, w) := alphaLevel opts st u
      (.succ u', st, w)
  | .max u v =>
      let (u', st, w1) := alphaLevel opts st u
      let (v', st, w2) := alphaLevel opts st v
      (.max u' v', st, w1 ++ w2)
  | .imax u v =>
      let (u', st, w1) := alphaLevel opts st u
      let (v', st, w2) := alphaLevel opts st v
      (.imax u' v', st, w1 ++ w2)
  | .param n =>
      if !opts.canonicalizeUniverses then (.param n, st, #[])
      else
        match st.universes[n]? with
        | some i => (.param (Name.mkSimple s!"u{i}"), st, #[])
        | none =>
            let i := st.universeCounter
            let st := { st with
              universeCounter := i + 1
              universes := st.universes.insert n i }
            (.param (Name.mkSimple s!"u{i}"), st, #[])
  | .mvar m =>
      let (st, w) := warnOnce st s!"search-view: universe metavariable ?{m.name} preserved"
      (.mvar m, st, w)

partial def alphaExpr (opts : AlphaExprOptions) (st : AlphaExprState) (e : Expr) :
    Expr × AlphaExprState × Array String :=
  match e with
  | .mdata _ inner => alphaExpr opts st inner
  | .const name levels =>
      Id.run do
        let mut levels' : List Level := []
        let mut st' := st
        let mut warnings : Array String := #[]
        for level in levels do
          let (level', stNext, w) := alphaLevel opts st' level
          levels' := levels' ++ [level']
          st' := stNext
          warnings := warnings ++ w
        return (.const name levels', st', warnings)
  | .sort level =>
      let (level', st', w) := alphaLevel opts st level
      (.sort level', st', w)
  | .lit value => (.lit value, st, #[])
  | .fvar id =>
      if !opts.canonicalizeFVars then (.fvar id, st, #[])
      else
        match st.fvars[id]? with
        | some id' => (.fvar id', st, #[])
        | none =>
            let i := st.fvarCounter
            let id' := FVarId.mk (Name.mkSimple s!"fv{i}")
            let st := { st with fvarCounter := i + 1, fvars := st.fvars.insert id id' }
            (.fvar id', st, #[])
  | .mvar id =>
      let (st, w) := warnOnce st s!"search-view: delayed metavariable ?{id.name} preserved"
      (.mvar id, st, w)
  | .bvar idx => (.bvar idx, st, #[])
  | .app fn arg =>
      let (fn', st1, w1) := alphaExpr opts st fn
      let (arg', st2, w2) := alphaExpr opts st1 arg
      if let .lam _ _ body _ := fn' then
        -- Beta: the argument is already normalized; normalize the contracted
        -- term so nested redexes are exposed.
        let (out, st3, w3) := alphaExpr opts st2 (body.instantiate1 arg')
        (out, st3, w1 ++ w2 ++ w3)
      else
        (.app fn' arg', st2, w1 ++ w2)
  | .lam _ type body _ =>
      let (type', st1, w1) := alphaExpr opts st type
      let (body', st2, w2) := alphaExpr opts st1 body
      -- Eta-reduction, chosen direction: contract `fun x => f x` to `f`.
      if let .app fn (.bvar 0) := body' then
        if !fn.hasLooseBVar 0 then
          (fn, st2, w1 ++ w2)
        else
          let (name, st3) := canonicalBinderName st2
          (.lam name type' body' .default, st3, w1 ++ w2)
      else
        let (name, st3) := canonicalBinderName st2
        (.lam name type' body' .default, st3, w1 ++ w2)
  | .forallE _ type body _ =>
      let (type', st1, w1) := alphaExpr opts st type
      let (body', st2, w2) := alphaExpr opts st1 body
      let (name, st3) := canonicalBinderName st2
      (.forallE name type' body' .default, st3, w1 ++ w2)
  | .letE _ _type value body _ =>
      -- Zeta: substitute the normalized value into the body, then normalize.
      let (value', st1, w1) := alphaExpr opts st value
      let (body', st2, w2) := alphaExpr opts st1 (body.instantiate1 value')
      (body', st2, w1 ++ w2)
  | .proj structName fieldIndex inner =>
      let (inner', st', w) := alphaExpr opts st inner
      (.proj structName fieldIndex inner', st', w)

/-- Pure best-effort search-view expression normalizer.  Warnings are returned
rather than printed.  This does **not** call `instantiateAll`; use
`searchViewNormalizeV3` for the full pipeline. -/
def searchViewNormalizeExprV3 (e : Expr) (opts : AlphaExprOptions := {}) :
    Expr × Array String :=
  let (e', _, warnings) := alphaExpr opts {} e
  (e', warnings)

/-- Standalone expression alpha normalizer.  By default free variables are
renamed by first occurrence; this is useful for comparing closed/open terms
without a local context, but should not be used before graph construction. -/
def alphaNormalizeExprV3 (e : Expr) (opts : AlphaExprOptions := { canonicalizeFVars := true }) :
    Expr × Array String :=
  searchViewNormalizeExprV3 e opts

/-- Full v3 search-view normalization: essentialize with the v1/v2 pipeline,
then apply the documented structural normal form.  Every failure or preserved
delayed mvar is in the returned warnings. -/
def searchViewNormalizeV3 (e : Expr) (label : String := "expression") :
    MetaM (Expr × Array String) := do
  let (e', essentializeWarnings) ← essentializeV3 e label
  let (e'', normalizeWarnings) := searchViewNormalizeExprV3 e'
  return (e'', essentializeWarnings ++ normalizeWarnings)

/-! ## Schema-3 canonical form (`alphaNormalizeV3`) -/

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

structure RawEdge where
  src : Nat
  type : String
  dst : Nat

def adjacencyOf (nodeCount : Nat) (edges : Array RawEdge) : Array (Array (String × Nat)) := Id.run do
  let mut adjacency : Array (Array (String × Nat)) := Array.replicate nodeCount #[]
  for edge in edges do
    if edge.src < nodeCount && edge.dst < nodeCount then
      adjacency := adjacency.set! edge.src ((adjacency[edge.src]!).push (edge.type, edge.dst))
  let mut sorted : Array (Array (String × Nat)) := Array.replicate nodeCount #[]
  for i in [:nodeCount] do
    sorted := sorted.set! i ((adjacency[i]!).qsort fun a b => edgeRank a.1 < edgeRank b.1)
  return sorted

structure CanonState where
  canon : Std.HashMap Nat Nat := {}
  order : Array Nat := #[]
  fvarCanon : Std.HashMap Nat Nat := {}
  fvarNodes : Array Nat := #[]
  mvarCanon : Std.HashMap Nat Nat := {}
  mvarNodes : Array Nat := #[]

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

def goalTableOf (graph : Json) : Array (String × Nat) :=
  let goals := arrFieldD graph "goals"
  if goals.isEmpty then #[("", jsonNatD graph "root" 0)]
  else goals.map fun g => (jsonStrD g "goal_id" "", jsonNatD g "root" 0)

def fvarTableOf (graph : Json) : Array (Nat × Nat × Nat × Option Nat) :=
  (arrFieldD graph "fvars").map fun f =>
    (jsonNatD f "index", jsonNatD f "node", jsonNatD f "type_node",
     if (f.getObjValD "value_node").isNull then none else some (jsonNatD f "value_node"))

def goalIndexOf (goals : Array (String × Nat)) (goalId : String) : Option Nat :=
  goals.findIdx? fun (id, _) => id == goalId

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

def sortPairs (pairs : Array (Nat × Nat)) : Array (Nat × Nat) :=
  pairs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def constantTableV3 (graph : Json) : Array (String × String × Nat) :=
  (arrFieldD graph "constants").map fun c =>
    (jsonStrD c "name" "", jsonStrD c "global_id" "", jsonNatD c "node" 0)

/-- Universe names are presentation identifiers in a graph payload.  For graph
alpha equivalence we rename them by first occurrence in canonical node order,
exactly as the term normalizer does.  This is deliberately a small scanner over
the strings produced by `GoalGraphCore.levelToString`; it only looks inside
`sort` payloads and `const` level brackets, never at constant names. -/
private structure UniverseNames where
  names : Std.HashMap String Nat := {}
  next : Nat := 0

private def isUniverseNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\''

private def takeUniverseName (cs : List Char) (acc : List Char) : String × List Char :=
  match cs with
  | [] => (String.ofList acc.reverse, [])
  | c :: rest =>
      if isUniverseNameChar c then takeUniverseName rest (c :: acc)
      else (String.ofList acc.reverse, c :: rest)

private def reservedUniverseToken (name : String) : Bool :=
  name == "Sort" || name == "Type" || name == "Prop" ||
  name == "max" || name == "imax" || name == "succ" ||
  name.toList.all Char.isDigit

private partial def renameUniverseText (st : UniverseNames) (text : String) :
    String × UniverseNames :=
  let rec go (st : UniverseNames) (out : List Char) (cs : List Char) :
      String × UniverseNames :=
    match cs with
    | [] => (String.ofList out.reverse, st)
    | c :: rest =>
        if isUniverseNameChar c then
          let (name, rest') := takeUniverseName (c :: rest) []
          let (mapped, st') :=
            if reservedUniverseToken name then (name, st)
            else
              match st.names[name]? with
              | some i => (s!"u{i}", st)
              | none =>
                  let i := st.next
                  (s!"u{i}", { st with names := st.names.insert name i, next := i + 1 })
          go st' (mapped.toList.reverse ++ out) rest'
        else
          go st (c :: out) rest
  go st [] text.toList

private def renameConstPayload (st : UniverseNames) (payload : String) :
    String × UniverseNames :=
  match payload.splitOn "[" with
  | [name, rest] =>
      match rest.splitOn "]" with
      | [levels, tail] =>
          let (levels', st') := renameUniverseText st levels
          (s!"{name}[{levels'}]{tail}", st')
      | _ => (payload, st)
  | _ => (payload, st)

private def renameCanonicalNodePayload (st : UniverseNames) (kind payload : String) :
    String × UniverseNames :=
  if kind == "sort" then renameUniverseText st payload
  else if kind == "const" then renameConstPayload st payload
  else (payload, st)

/-- Apply universe alpha-renaming to the already-rendered `node` lines.  The
canonical traversal order is the line order, so this is deterministic and
independent of the original parameter names. -/
private def renameUniverseLines (lines : Array String) : Array String := Id.run do
  let mut st : UniverseNames := {}
  let mut out : Array String := #[]
  for line in lines do
    match line.splitOn " " with
    | "node" :: id :: kind :: rest =>
        let payload := String.intercalate " " rest
        let (payload', st') := renameCanonicalNodePayload st kind payload
        out := out.push s!"node {id} {kind} {payload'}"
        st := st'
    | _ => out := out.push line
  return out

/-- Metadata-free canonical form of a schema-3 graph.  It preserves everything
semantic: node kinds/payloads, edges, goal roots, fvar table, constant names
**and global ids**, coupled `groups`, coupled `goal_edges`, and loci.  It drops
only presentation/provenance fields (`theorem`, `module`, goal ids, display
names, positions/depths, parse warnings).  Universe parameter names are
alpha-renamed by first occurrence to `u0`, `u1`, ... in canonical node order. -/
def alphaNormalizeV3 (graph : Json) : Except String String := do
  let nodeJson := arrFieldD graph "nodes"
  let nodes : Array RawNode := nodeJson.map rawNodeOf
  let edges : Array RawEdge := (arrFieldD graph "edges").map fun e =>
    { src := jsonNatD e "src", type := jsonStrD e "type", dst := jsonNatD e "dst" }
  let adjacency := adjacencyOf nodes.size edges
  let goals := goalTableOf graph
  let fvarTable := fvarTableOf graph
  let constantTable := constantTableV3 graph
  let roots := goals.map (·.2)
  let mut st := dfsVisit nodes adjacency roots.toList {}
  for (_index, node, typeNode, valueNode?) in fvarTable do
    st := dfsVisit nodes adjacency [node, typeNode] st
    if let some value := valueNode? then
      st := dfsVisit nodes adjacency [value] st
  for i in [:nodes.size] do
    st := dfsVisit nodes adjacency [i] st
  let canon := fun (n : Nat) => st.canon.getD n n
  let mut lines : Array String := #["exprgraph-v3-canonical"]
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
  for (name, gid, node) in constantTable.qsort (fun a b => a.1 < b.1) do
    lines := lines.push s!"const {name} {gid} {canon node}"
  let mut fvarIndexToCanon : Std.HashMap Nat Nat := {}
  let mut fvarLines : Array (Nat × Nat × Nat × Option Nat) := #[]
  for (index, node, typeNode, valueNode?) in fvarTable do
    let canonIndex := st.fvarCanon.getD node index
    fvarIndexToCanon := fvarIndexToCanon.insert index canonIndex
    fvarLines := fvarLines.push (canonIndex, canon node, canon typeNode, valueNode?.map canon)
  for (index, node, typeNode, valueNode?) in fvarLines.qsort (fun a b => a.1 < b.1) do
    let base := s!"fvar {index} node {node} type {typeNode}"
    match valueNode? with
    | some value => lines := lines.push s!"{base} value {value}"
    | none => lines := lines.push base
  let coupled := graph.getObjValD "coupled"
  let groups : Array Json :=
    match coupled.getArr? with
    | .ok _ => arrFieldD graph "coupled"  -- defensive v2 compatibility
    | .error _ => arrFieldD coupled "groups"
  for group in groups do
    let goalIndices : Array Nat := Array.filterMap
      (fun g => goalIndexOf goals ((g.getStr?).toOption.getD "")) (arrFieldD group "goals")
    let fvarIndices : Array Nat := Array.filterMap
      (fun v => fvarIndexToCanon[jsonAsNatD v]?) (arrFieldD group "fvars")
    let join (xs : Array Nat) : String := String.intercalate "," (xs.map toString).toList
    lines := lines.push s!"coupled-group [{join (goalIndices.qsort (· < ·))}] [{join (fvarIndices.qsort (· < ·))}]"
  if let .ok _ := coupled.getArr? then
    pure ()
  else
    for edge in arrFieldD coupled "goal_edges" do
      let src? := goalIndexOf goals (jsonStrD edge "src" "")
      let dst? := goalIndexOf goals (jsonStrD edge "dst" "")
      match src?, dst? with
      | some src, some dst =>
          let fvarIndices : Array Nat := Array.filterMap
            (fun v => fvarIndexToCanon[jsonAsNatD v]?) (arrFieldD edge "fvars")
          let join (xs : Array Nat) : String := String.intercalate "," (xs.map toString).toList
          lines := lines.push s!"goal-edge {src} {dst} [{join (fvarIndices.qsort (· < ·))}]"
      | _, _ => lines := lines.push "goal-edge <missing-goal>"
  let mut locusPairs : Array (Nat × Nat) := #[]
  for entry in arrFieldD graph "loci" do
    let goalIndex := goalIndexOf goals (jsonStrD entry "goal_id" "") |>.getD 0
    locusPairs := locusPairs.push (goalIndex, canon (jsonNatD entry "node"))
  for (goalIndex, node) in sortPairs locusPairs do
    lines := lines.push s!"locus {goalIndex} {node}"
  return String.intercalate "\n" (renameUniverseLines lines).toList

def alphaEquivalentV3 (left right : Json) : Except String Bool := do
  let leftForm ← alphaNormalizeV3 left
  let rightForm ← alphaNormalizeV3 right
  return leftForm == rightForm

/-- Graph-level counts for samples and regression checks. -/
def stats (graph : Json) : Except String Json := do
  let goals := arrFieldD graph "goals"
  let nodes := arrFieldD graph "nodes"
  let edges := arrFieldD graph "edges"
  let loci := arrFieldD graph "loci"
  let fvars := arrFieldD graph "fvars"
  let constants := arrFieldD graph "constants"
  let coupled := graph.getObjValD "coupled"
  let groups := arrFieldD coupled "groups"
  let goalEdges := arrFieldD coupled "goal_edges"
  let shared := fvars.filter fun f => (arrFieldD f "goals").size ≥ 2
  let coupling := Array.foldl (fun acc c => acc + (arrFieldD c "goals").size) 0 groups
  let couplingFvars := Array.foldl (fun acc c => acc + (arrFieldD c "fvars").size) 0 groups
  return Json.mkObj [
    ("goals", Lean.toJson goals.size),
    ("nodes", Lean.toJson nodes.size),
    ("edges", Lean.toJson edges.size),
    ("loci", Lean.toJson loci.size),
    ("fvars", Lean.toJson fvars.size),
    ("shared_fvars", Lean.toJson shared.size),
    ("coupled_groups", Lean.toJson groups.size),
    ("coupled_goals", Lean.toJson coupling),
    ("coupled_fvars", Lean.toJson couplingFvars),
    ("goal_edges", Lean.toJson goalEdges.size),
    ("constants", Lean.toJson constants.size)]

end ExprGraphV3
