/-
  StructuredTraceV4: export ONE theorem's atomization trace as schema-4 JSONL.

  This is the schema-4 successor of `Standalone/StructuredTraceOne.lean`.  The
  old exporter is left untouched (Gate 1.2 output directories are never
  overwritten); this file is a separate producer that adds the training inputs
  the schema-3 traces were missing.

  Usage:
    lean --run Standalone/StructuredTraceV4.lean MODULE THEOREM OUTPUT_PATH

  Environment:
    NAZRIN_STRUCT_MAX_HEARTBEATS   heartbeat cap for this theorem (default 200000)
    NAZRIN_STRUCT_MAX_STEPS        atomization step cap (default 3000, paper §VI p.8)
    NAZRIN_STRUCT_RUN_ID           opaque run id copied into every record
    NAZRIN_STRUCT_STEP_SCHEMA      envelope schema: 3 (default, Gate 1.2/1.3
                                   compatible) or 4 (strict schema-4 envelope)
    NAZRIN_STRUCT_PREMISE_MODE     "graph" (default: the candidate table is the
                                   pre-step graph's constant table, the observed
                                   label is never appended) or "append" (append
                                   the observed label, marked `origin=label`)
    NAZRIN_STRUCT_EMIT_LOCI        accepted for compatibility; schema 4 always
                                   emits the full locus list

  Output (one JSON object per line, UTF-8):
    {"schema":3,"schema_version":4,"record":"step",...}    one per atomization step
    {"schema":3,"schema_version":4,"record":"theorem",...} one final summary record

  Reasons for every addition (paper anchors; page numbers are PDF pages of
  `Nazrin:_An_Atomic_Neural_Proof_Automation_Tactic_in_Lean_4.pdf`, all 12 pages
  extracted with `pdftotext -layout` and read):

  * §V-A pp.6–7 + Fig. 5: an ExprGraph has one vertex per rewritable
    subexpression (locus), and a goal state is a disjunction of such graphs.  A
    trace step therefore has to carry the graph, not a position count.
  * §V-A Fig. 6 + §III-A pp.2–3: coupled goals cross-reference each other's
    fvars and search is a DAG, not a tree; the graph must cover the whole
    pre-step goal state and emit `coupled`.
  * §V-B p.7 Fig. 4: the NPA has a premise head (green), a free-variable head
    (blue) and a locus head (yellow).  Each needs an ordered candidate table; a
    label is an index into that table.
  * §V p.8: "translating locus indices into subexpression positions and
    translating free variable indices to free variable names" — the label is the
    index, the graph node/position is the replay form.  Hypothesis-scope rewrites
    (§IV p.6 Table II: rewrite is semi-prograde *or* semi-retrograde) need
    positions inside a hypothesis type, which target-only `loci` cannot represent.
  * Appendix A p.11 Fig. 9: `exact(x)` accepts a constant *or* a free variable;
    that is why `exact`/`apply` steps with a local-hypothesis payload keep a
    `free_variable` label (a model-head gap, reported, never rewritten).
  * §VI p.8: 3,000-step cap and theorem-level search budget — the data is
    produced at theorem granularity without changing the atomizer.

  Contract (unchanged from schema 3, re-checked against the new tables):
  * A label is emitted only if it is present in the tactic payload AND belongs to
    the ordered candidate table of the goal.  `free_variable` is checked against
    the graph's fvar table for the current goal; `premise` against the graph's
    constant table; `locus` against the graph's loci (target) or the hypothesis
    type's positions (hypothesis).  Otherwise the parameter is dropped, listed in
    `rejected`, and counted.
  * `premise` labels that resolve to the target theorem itself or to a name
    derived from it (`T.eq_1`, `T._unary`, `_private...T...`) are dropped and
    counted (`target_reference_dropped`).
  * **Fail closed, never fabricate.**  If the graph cannot be built, or a
    candidate table cannot be derived from it, or a locus label does not address
    the emitted candidate list, the step record carries an `error` object and
    **no** `goal_state_graph`, `premise_candidates`, `candidates.locus_candidates`
    or `goal_state`.  No placeholder graph, empty candidate table or guessed
    label is ever written.
-/
import Standalone.AtomizerCore
import Standalone.GoalGraphCore
import Standalone.ExprGraphV3
import Lean.Data.Json

open Lean Nazrin

namespace StructuredTraceV4

/-- The schema-4 generation number stamped on every record. -/
def schemaVersion : Nat := 4

/-! ## JSON helpers (a missing or mistyped field returns the default) -/

def jStr? (j : Json) (key : String) : Option String :=
  (j.getObjVal? key).toOption.bind (fun v => v.getStr?.toOption)

def jNat? (j : Json) (key : String) : Option Nat :=
  (j.getObjVal? key).toOption.bind (fun v => v.getNat?.toOption)

def jArr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjVal? key).toOption.bind (fun v => v.getArr?.toOption)

def jStr (j : Json) (key : String) (default : String := "") : String :=
  (jStr? j key).getD default

def jNat (j : Json) (key : String) (default : Nat := 0) : Nat :=
  (jNat? j key).getD default

def jArr (j : Json) (key : String) : Array Json :=
  (jArr? j key).getD #[]

def jArrStrings (j : Json) (key : String) : Array String :=
  (jArr j key).filterMap (fun v => v.getStr?.toOption)

/-! ## Environment -/

def natEnv (name : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => pure default
  | some raw =>
    match raw.toNat? with
    | some 0 => pure default
    | some value => pure value
    | none => pure default

def strEnv (name : String) (default : String) : IO String := do
  match ← IO.getEnv name with
  | some value => if value.isEmpty then pure default else pure value
  | none => pure default

def debugEnabled : IO Bool := do
  match ← IO.getEnv "NAZRIN_STRUCT_DEBUG" with
  | some "1" => pure true
  | some "true" => pure true
  | _ => pure false

def debugLog (message : String) : IO Unit := do
  if ← debugEnabled then IO.eprintln s!"[v4] {message}"

/-- FNV-1a 64-bit fingerprint over a sequence of strings.  Deterministic; used
for the locus candidate fingerprint.  Per-item constant ids come from
`ExprGraphV3.globalConstantId`, which is the schema-3 identity. -/
def fingerprint (parts : Array String) : String :=
  let modulus := 18446744073709551616
  let h := parts.foldl (init := 14695981039346656037) fun h s =>
    s.toList.foldl (init := h) fun h c =>
      ((h ^^^ c.toNat) * 1099511628211) % modulus
  let digits := Nat.toDigits 16 h
  let padded := List.replicate (16 - digits.length) '0' ++ digits
  String.ofList padded

/-- The stable schema-3 global constant id (16 lowercase hex digits). -/
def constantId (name : String) : String :=
  ExprGraphV3.globalConstantId name.toName

/-! ## Parsed schema-3 graph tables

The embedded graph JSON is the single source of truth: every candidate table
below is read back from it, so a record's tables and its graph cannot disagree. -/

structure GoalRow where
  goalId : String
  root : Nat
  fvarCount : Nat
deriving Inhabited

structure FvarRow where
  index : Nat
  name : String
  node : Nat
  typeNode : Nat
  valueNode : Option Nat := none
  goals : Array String := #[]
deriving Inhabited

structure ConstRow where
  name : String
  globalId : String
  node : Nat
deriving Inhabited

structure LocusRow where
  goalId : String
  position : String
  node : Nat
deriving Inhabited

structure GraphTables where
  goals : Array GoalRow := #[]
  fvars : Array FvarRow := #[]
  constants : Array ConstRow := #[]
  loci : Array LocusRow := #[]
  goalEdges : Array Json := #[]
  groups : Array Json := #[]
  warnings : Array String := #[]
  nodeCount : Nat := 0
  edgeCount : Nat := 0
deriving Inhabited

def parseGraphTables (graph : Json) : GraphTables := Id.run do
  let mut goals : Array GoalRow := #[]
  for entry in jArr graph "goals" do
    goals := goals.push {
      goalId := jStr entry "goal_id"
      root := jNat entry "root"
      fvarCount := jNat entry "fvar_count" }
  let mut fvars : Array FvarRow := #[]
  for entry in jArr graph "fvars" do
    fvars := fvars.push {
      index := jNat entry "index"
      name := jStr entry "name"
      node := jNat entry "node"
      typeNode := jNat entry "type_node"
      valueNode := jNat? entry "value_node"
      goals := jArrStrings entry "goals" }
  let mut constants : Array ConstRow := #[]
  for entry in jArr graph "constants" do
    constants := constants.push {
      name := jStr entry "name"
      globalId := jStr entry "global_id"
      node := jNat entry "node" }
  let mut loci : Array LocusRow := #[]
  for entry in jArr graph "loci" do
    loci := loci.push {
      goalId := jStr entry "goal_id"
      position := jStr entry "position"
      node := jNat entry "node" }
  let coupled := match graph.getObjVal? "coupled" with
    | .ok value => value
    | .error _ => Json.mkObj []
  return {
    goals := goals
    fvars := fvars
    constants := constants
    loci := loci
    goalEdges := jArr coupled "goal_edges"
    groups := jArr coupled "groups"
    warnings := jArrStrings graph "parse_warnings"
    nodeCount := (jArr graph "nodes").size
    edgeCount := (jArr graph "edges").size }

/-! ## Graph node walker (hypothesis-scope locus nodes)

Schema-3 `loci` only covers goal targets; a rewrite on a hypothesis needs the node
of a subexpression inside that hypothesis' type, which lives in the graph's
`fvar_type` metadata subgraph.  The walker recovers `relative position -> node id`
by following the same structural edges `GoalGraphCore.buildExpr` emitted.  A leaf
node may be shared by condensation; the walk still lands on the correct node. -/

structure NodeWalk where
  kinds : Array String := #[]
  children : Std.HashMap Nat (Array (String × Nat)) := {}
deriving Inhabited

/-- The structural edge a child coordinate takes for a node kind.  Mirrors
`GoalGraphCore.buildExpr` exactly. -/
def childEdgeType (kind : String) (coord : Nat) : Option String :=
  match kind, coord with
  | "app", 0 => some "app_fn"
  | "app", 1 => some "app_arg"
  | "lam", 0 => some "binder_type"
  | "lam", 1 => some "binder_body"
  | "forallE", 0 => some "binder_type"
  | "forallE", 1 => some "binder_body"
  | "letE", 0 => some "let_type"
  | "letE", 1 => some "let_value"
  | "letE", 2 => some "let_body"
  | "proj", 0 => some "proj_struct"
  | _, _ => none

def mkNodeWalk (graph : Json) : NodeWalk := Id.run do
  let mut kinds : Array String := #[]
  for node in jArr graph "nodes" do
    kinds := kinds.push (jStr node "kind")
  let mut children : Std.HashMap Nat (Array (String × Nat)) := {}
  for edge in jArr graph "edges" do
    let src := jNat edge "src"
    let dst := jNat edge "dst"
    let typ := jStr edge "type"
    children := children.insert src ((children.getD src #[]).push (typ, dst))
  return { kinds, children }

partial def NodeWalk.walk (walk : NodeWalk) (start : Nat) (coords : Array Nat) : Option Nat :=
  let rec go (node : Nat) (i : Nat) : Option Nat :=
    if i >= coords.size then
      some node
    else
      let kind := walk.kinds[node]?.getD ""
      match childEdgeType kind coords[i]! with
      | none => none
      | some edgeType =>
        match (walk.children.getD node #[]).find? (fun (typ, _) => typ == edgeType) with
        | none => none
        | some (_, dst) => go dst (i + 1)
  go start 0

/-! ## Free-variable candidates -/

structure FVarCandidates where
  names : Array String
  index : Std.HashMap FVarId Nat

structure FVarNodeRow where
  name : String
  graphIndex : Nat
  node : Nat
  typeNode : Nat
deriving Inhabited

def FVarNodeRow.json (row : FVarNodeRow) : Json :=
  Json.mkObj [
    ("name", toJson row.name), ("graph_index", toJson row.graphIndex),
    ("node", toJson row.node), ("type_node", toJson row.typeNode)]

/-- Ordered free-variable table of one goal, taken from the graph's global fvar
table filtered by the goal id (table order == the graph's order).  Fvar ids are
recovered from the same `displayNamesFor` map the graph builder used. -/
def fvarTableFor (fvars : Array FvarRow) (names : Std.HashMap FVarId String)
    (goalId : String) : Except String (FVarCandidates × Array FVarNodeRow) := do
  let mut byName : Std.HashMap String FVarId := {}
  for (id, name) in names.toList do
    if byName.contains name then
      -- `displayNamesFor` makes names unique by construction; a duplicate means
      -- the caller passed a different map than the graph builder used.
      throw s!"duplicate display name {name}"
    byName := byName.insert name id
  let mut out : Array String := #[]
  let mut index : Std.HashMap FVarId Nat := {}
  let mut rows : Array FVarNodeRow := #[]
  for row in fvars do
    if row.goals.contains goalId then
      let some id := byName[row.name]?
        | throw s!"fvar {row.name} of goal {goalId} is missing from the display-name map"
      if index.contains id then
        throw s!"goal {goalId} declares fvar {row.name} twice in the graph table"
      index := index.insert id out.size
      out := out.push row.name
      rows := rows.push {
        name := row.name
        graphIndex := row.index
        node := row.node
        typeNode := row.typeNode }
  return ({ names := out, index }, rows)

/-! ## Locus positions -/

def path (p : SubExpr.Pos) : String := GoalGraphCore.posToPath p

/-- Schema-4 locus spellings use the dataset contract's normalized root (`"root"`
instead of the empty string), because `convert_structured_trace.normalize_position`
treats `"root"` as the root position and a schema-3 graph keeps `""` in `loci`.
Every locus candidate, locus label and `parameters.locus` uses this spelling;
the graph's own `loci` table is untouched schema 3. -/
def locusPos (p : SubExpr.Pos) : String :=
  let raw := path p
  if raw.isEmpty then "root" else raw

def normalizeLocusString (raw : String) : String :=
  if raw.isEmpty then "root" else raw

/-- Every rewritable subexpression of `e`, in the same post-order the goal graph
uses for its `loci` table (children first, root last).  `mdata` is transparent,
exactly as in `GoalGraphCore.buildExpr`. -/
partial def lociOf (e : Expr) (p : SubExpr.Pos) : Array SubExpr.Pos :=
  match e with
  | .mdata _ inner => lociOf inner p
  | .const .. | .sort .. | .lit .. | .fvar .. | .mvar .. | .bvar .. => #[]
  | .app fn arg =>
    lociOf fn p.pushAppFn ++ #[p.pushAppFn] ++
    lociOf arg p.pushAppArg ++ #[p.pushAppArg]
  | .lam _ type body _ =>
    lociOf type p.pushBindingDomain ++ #[p.pushBindingDomain] ++
    lociOf body p.pushBindingBody ++ #[p.pushBindingBody]
  | .forallE _ type body _ =>
    lociOf type p.pushBindingDomain ++ #[p.pushBindingDomain] ++
    lociOf body p.pushBindingBody ++ #[p.pushBindingBody]
  | .letE _ type value body _ =>
    lociOf type p.pushLetVarType ++ #[p.pushLetVarType] ++
    lociOf value p.pushLetValue ++ #[p.pushLetValue] ++
    lociOf body p.pushLetBody ++ #[p.pushLetBody]
  | .proj _ _ inner =>
    lociOf inner p.pushProj ++ #[p.pushProj]

/-- Locus candidates of one goal's target, straight from the graph's own `loci`. -/
def targetLocusItems (tables : GraphTables) (goalId : String) :
    Array (String × Nat) :=
  (tables.loci.filter (fun row => row.goalId == goalId)).map
    (fun row => (normalizeLocusString row.position, row.node))

/-- Locus candidates of one hypothesis type: every position of the type
expression, each resolved to its graph node by walking the `fvar_type` subgraph.
Fails closed (no partial list) if any position cannot be resolved. -/
def hypothesisLocusItems (walk : NodeWalk) (typeNode : Nat) (type : Expr) :
    Except String (Array (String × Nat)) := do
  let positions := (lociOf type .root).push .root
  let mut out : Array (String × Nat) := #[]
  for pos in positions do
    match walk.walk typeNode pos.toArray with
    | some node => out := out.push (locusPos pos, node)
    | none =>
      throw s!"hypothesis locus {locusPos pos} has no node in the graph's fvar_type subgraph"
  return out

/-! ## Tactic payload -> checked labels -/

inductive Head where
  | const (name : Name)
  | fvar (id : FVarId)
  | other

def headOf (e : Expr) : Head :=
  match e.getAppFn with
  | .const name _ => .const name
  | .fvar id => .fvar id
  | _ => .other

structure Rejection where
  field : String
  value : String
  reason : String

def rejectionJson (r : Rejection) : Json :=
  Json.mkObj [("field", toJson r.field), ("value", toJson r.value),
              ("reason", toJson r.reason)]

/-- The target theorem itself or a name derived from it (`T.eq_1`, `T._unary`,
`T._proof_1`, `T.match_1`, `_private...T...`). -/
def isTargetName (target : Name) (name : Name) : Bool :=
  let t := target.toString
  let n := name.toString
  n == t || n.startsWith (t ++ ".") || (n.startsWith "_private" && n.contains t)

structure Extracted where
  kind : String
  params : Array (String × Json) := #[]
  labels : Array (String × Json) := #[]
  rejected : Array Rejection := #[]
  unmodeled : Bool := false
  targetDropped : Nat := 0

def Extracted.addParam (x : Extracted) (k : String) (v : Json) : Extracted :=
  { x with params := x.params.push (k, v) }

def Extracted.addLabel (x : Extracted) (k : String) (v : Json) : Extracted :=
  { x with labels := x.labels.push (k, v) }

def Extracted.reject (x : Extracted) (field value reason : String) : Extracted :=
  { x with rejected := x.rejected.push { field, value, reason } }

/-- Free-variable label; emitted only when the id is in the graph's fvar table for
the current goal.  Never falls back to `FVarId.name`. -/
def Extracted.addFVar (fvc : FVarCandidates) (x : Extracted) (key : String)
    (source : String) (id : FVarId) : Extracted :=
  match fvc.index[id]? with
  | some i =>
    let name := fvc.names[i]!
    if name.isEmpty then
      x.reject key "" "empty_label"
    else
      x.addParam key (toJson name)
       |>.addLabel key (Json.mkObj [
            ("name", toJson name), ("index", toJson i), ("source", toJson source)])
  | none =>
    x.reject key id.name.toString "not_in_graph_fvar_table"

/-- Constant premise: the parameter is added only together with a label, so a
dropped target-derived name can never leave an unlabelled pointer parameter. -/
def Extracted.addConstPremise (target : Name) (x : Extracted) (name : Name) : Extracted :=
  if isTargetName target name then
    { x.reject "premise" name.toString "target_reference_dropped" with
        targetDropped := x.targetDropped + 1 }
  else
    x.addParam "premise" (toJson name.toString)
     |>.addLabel "premise" (Json.mkObj [
          ("name", toJson name.toString), ("source", toJson "payload_const")])

def nameMode (name : Name) : Json :=
  toJson (if name.isAnonymous then "anonymous" else "explicit")

/-- Extract the modeled parameters and checked labels from a tactic payload. -/
def extract (target : Name) (fvc : FVarCandidates) (tactic : AtomicTactic) : Extracted :=
  let base : Extracted := { kind := AtomicTactic.kind tactic }
  match tactic with
  | .intro name =>
    base.addParam "name_mode" (nameMode name)
  | .pi name =>
    base.addParam "name_mode" (nameMode name)
  | .revert fvarId =>
    base.addFVar fvc "free_variable" "payload_fvar" fvarId
  | .apply e | .motivatedApply e | .exact e =>
    match headOf e with
    | .const name => base.addConstPremise target name
    | .fvar id =>
      let x := base.addFVar fvc "free_variable" "payload_fvar_head" id
      x.addParam "argument_mode" (toJson "free_variable")
    | .other =>
      { base with unmodeled := true }.reject "premise" "" "head_not_const_or_fvar"
  | .generalize name e =>
    let x := base.addParam "name_mode" (nameMode name)
    match e with
    | .fvar id => x.addFVar fvc "free_variable" "payload_fvar" id
    | _ => { x with unmodeled := true }.reject "free_variable" "" "head_not_fvar"
  | .cases major =>
    let x := base.addParam "cases_mode" (toJson "constructors")
    match major with
    | .fvar id => x.addFVar fvc "free_variable" "payload_fvar" id
    | _ => { x with unmodeled := true }.reject "free_variable" "" "major_not_fvar"
  | .induction major recursor =>
    let x := base.addParam "induction_mode"
      (toJson (if recursor.isAnonymous then "ordinary" else "using"))
    let x := if recursor.isAnonymous then x else x.addConstPremise target recursor
    match major with
    | .fvar id => x.addFVar fvc "free_variable" "payload_fvar" id
    | _ => { x with unmodeled := true }.reject "free_variable" "" "major_not_fvar"
  | .rewrite fvarId? pos heq0 symm allOccs =>
    let x := base.addParam "direction" (toJson (if symm then "backward" else "forward"))
      |>.addParam "occurrence" (toJson (if allOccs then "all" else "first"))
      |>.addParam "locus" (toJson (locusPos pos))
      |>.addParam "target_mode" (toJson (if fvarId?.isSome then "hypotheses" else "goal"))
    let x := match headOf heq0 with
      | .const name => x.addConstPremise target name
      | .fvar id => x.addFVar fvc "free_variable" "payload_fvar_rule" id
      | .other =>
        { x with unmodeled := true }.reject "premise" "" "head_not_const_or_fvar"
    match fvarId? with
    | some id => x.addFVar fvc "site_free_variable" "payload_fvar_site" id
    | none => x
  | .generalizeAt _binderName pos =>
    base.addParam "locus" (toJson (path pos))
      |>.addParam "target_mode" (toJson "goal")
  | .unfold fvarId? name =>
    -- Schema-4 fix: Gate 1.2 emitted `parameters.premise` for `unfold` without a
    -- `labels.premise`, which made those steps unconvertible.  The unfolded
    -- constant is a real premise, so the label is emitted with the parameter (and
    -- dropped, with the parameter, when it is target-derived).
    let x := base.addParam "target_mode"
      (toJson (if fvarId?.isSome then "hypotheses" else "goal"))
    let x := x.addConstPremise target name
    match fvarId? with
    | some id => x.addFVar fvc "free_variable" "payload_fvar" id
    | none => x
  | .normalize | .reduceBeta =>
    base.addParam "target_mode" (toJson "goal")
  | .contradiction | .assumption | .decide | .refl | .inhabit | .tailArg => base
  | .define _ _ | .have _ _ | .let _ _ | .raw _ => { base with unmodeled := true }

/-! ## Premise candidate table

Default (`mode = "graph"`): the table is exactly the pre-step graph's constant
table (a real, state-local universe) and the observed label is never appended, so
`label ∈ table` is a genuine assertion.  When the label is absent the step keeps
its real table, records `label_in_table = false`, and Gate 1.3's converter rejects
that step — a counted gap, not a fabricated candidate.

`mode = "append"` appends the observed label with `origin = "label"`; that is the
leaky mode Gate 1.3's report warns about.  It exists for A/B measurement and is
never the default. -/

structure PremiseItem where
  name : String
  id : String
  origin : String
deriving Inhabited

structure PremiseResult where
  items : Array PremiseItem := #[]
  labelName : Option String := none
  labelIndex : Option Nat := none
  labelId : Option String := none
  labelInGraph : Bool := false
  appended : Bool := false
  missing : Bool := false
  mode : String := "graph"

def PremiseResult.json (r : PremiseResult) : Json :=
  Json.mkObj [
    ("mode", toJson r.mode),
    ("table_size", toJson r.items.size),
    ("label", match r.labelName with | some n => Json.str n | none => Json.null),
    ("label_in_table", toJson r.labelIndex.isSome),
    ("label_in_graph_constants", toJson r.labelInGraph),
    ("label_appended", toJson r.appended),
    ("label_missing", toJson r.missing),
    ("label_index", match r.labelIndex with | some i => toJson i | none => Json.null),
    ("label_id", match r.labelId with | some i => Json.str i | none => Json.null)]

def itemsJson (items : Array PremiseItem) : Json :=
  Json.arr (items.map fun item => Json.mkObj [
    ("name", toJson item.name), ("id", toJson item.id), ("origin", toJson item.origin)])

/-- Build the premise candidate table and re-check the extracted premise label
against it.  Returns the (possibly relabelled) extraction and the evidence. -/
def premiseTable (consts : Array ConstRow) (mode : String) (x : Extracted) :
    Extracted × PremiseResult :=
  let append := mode == "append"
  let label? : Option String :=
    match x.params.find? (fun (k, _) => k == "premise") with
    | some (_, v) => v.getStr?.toOption
    | none =>
      match x.labels.find? (fun (k, _) => k == "premise") with
      | some (_, v) => jStr? v "name"
      | none => none
  let graphItems : Array PremiseItem := consts.map fun c =>
    { name := c.name, id := c.globalId, origin := "graph" }
  let graphHit := match label? with
    | none => none
    | some name => consts.findIdx? (fun c => c.name == name)
  let (items, index?, appended, missing) :=
    match label?, graphHit with
    | none, _ => (graphItems, none, false, false)
    | some _, some _ => (graphItems, graphHit, false, false)
    | some name, none =>
      if append then
        ((graphItems.push { name := name, id := constantId name, origin := "label" }),
          some graphItems.size, true, false)
      else
        (graphItems, none, false, true)
  let labels := x.labels.filter (fun (k, _) => k != "premise")
  let x := match label?, index? with
    | some name, some i =>
      let item := items[i]!
      { x with labels := labels.push ("premise", Json.mkObj [
          ("name", toJson name), ("index", toJson i), ("id", toJson item.id),
          ("origin", toJson item.origin), ("source", toJson "payload_const")]) }
    | _, _ => { x with labels := labels }
  let result : PremiseResult := {
    items := items
    labelName := label?
    labelIndex := index?
    labelId := index?.map (fun i => items[i]!.id)
    labelInGraph := graphHit.isSome
    appended := appended
    missing := missing
    mode := mode }
  (x, result)

/-! ## Locus candidate table -/

structure LocusItem where
  position : String
  node : Nat
  scope : String
  scopeFvarName : Option String := none
  scopeFvarIndex : Option Nat := none
deriving Inhabited

def LocusItem.json (index : Nat) (item : LocusItem) : Json :=
  let base := [
    ("position", toJson item.position),
    ("index", toJson index),
    ("node", toJson item.node),
    ("scope", toJson item.scope)]
  let extra := match item.scopeFvarName, item.scopeFvarIndex with
    | some name, some fvarIndex => [
        ("scope_fvar", Json.mkObj [
          ("name", toJson name), ("index", toJson fvarIndex)])]
    | _, _ => []
  Json.mkObj (base ++ extra)

structure LocusResult where
  items : Array LocusItem := #[]
  scope : String := "goal"
  scopeFvarName : Option String := none
  scopeFvarIndex : Option Nat := none
  labelIndex : Option Nat := none
  labelPosition : Option String := none
  fingerprint : String := ""

def LocusResult.json (r : LocusResult) : Json :=
  Json.mkObj [
    ("scope", toJson r.scope),
    ("count", toJson r.items.size),
    ("label", match r.labelPosition with | some p => Json.str p | none => Json.null),
    ("index", match r.labelIndex with | some i => toJson i | none => Json.null),
    ("fingerprint", toJson r.fingerprint),
    ("scope_fvar", match r.scopeFvarName, r.scopeFvarIndex with
      | some name, some i => Json.mkObj [("name", toJson name), ("index", toJson i)]
      | _, _ => Json.null)]

/-- Assemble a locus result (with a fingerprinted position list) from a raw
(position, node) list for the given scope. -/
def mkLocusResult (raw : Array (String × Nat)) (scope : String)
    (fvarName? : Option String) (fvarIndex? : Option Nat) : LocusResult :=
  let items := raw.map fun (position, node) =>
    { position := position, node := node, scope := scope,
      scopeFvarName := fvarName?, scopeFvarIndex := fvarIndex? }
  { items := items
    scope := scope
    scopeFvarName := fvarName?
    scopeFvarIndex := fvarIndex?
    fingerprint := fingerprint (items.map (·.position)) }

/-- Attach the checked locus label.  A position outside the emitted scope fails
closed: the step is not representable, so no partial (locus-less) rewrite record
is produced. -/
def LocusResult.withLabel (r : LocusResult) (x : Extracted) (pos : String)
    (source : String) : Except String (LocusResult × Extracted) := do
  let some i := r.items.findIdx? (fun item => item.position == pos)
    | throw s!"locus position {pos} is not in the {r.scope} candidate list ({r.items.size} entries)"
  let item := r.items[i]!
  let label := Json.mkObj [
    ("position", toJson pos), ("index", toJson i), ("node", toJson item.node),
    ("scope", toJson r.scope), ("source", toJson source)]
  return ({ r with labelIndex := some i, labelPosition := some pos }, x.addLabel "locus" label)

/-! ## Heartbeat accounting

Graph construction and record assembly are exporter instrumentation, not
atomization.  They must neither consume the theorem's heartbeat budget (Gate 1.2
gave that budget to the atomizer alone, so consuming it here would fail theorems
that succeeded there) nor be limited by it.  The two wrappers below do exactly
that:

* `withHeartbeatBudget` runs an instrumentation action on a fresh, unlimited
  budget (heartbeat `0` means "no limit" in `Core.checkMaxHeartbeatsCore`).
* `withRefundedHeartbeats` rewinds the global heartbeat counter to its value
  before the action, so the atomizer's remaining budget is unchanged.

The refund is a deliberate, documented accounting choice: it does not change the
atomizer's input state, only the resource counter it is charged against.
-/

def withHeartbeatBudget {α : Type} (x : MetaM α) : MetaM α :=
  controlAt CoreM fun runInBase => do
    let initHeartbeats ← IO.getNumHeartbeats
    withReader (fun ctx : Core.Context =>
      { ctx with initHeartbeats := initHeartbeats, maxHeartbeats := 0 }) (runInBase x)

def withRefundedHeartbeats {α : Type} (x : MetaM α) : MetaM α := do
  let before ← IO.getNumHeartbeats
  let result ← x
  IO.setNumHeartbeats before
  return result

/-! ## Read-only graph build

Graph construction runs on a discarded `Meta.SavedState`: every metavariable
assignment, new metavariable, message and environment change it makes is rolled
back, so the atomizer sees exactly the state it would have seen without the graph.
This is Gate 1.3's checklist item "build it on a discarded MetaM state". -/
def buildGraphReadOnly (theoremName : Name) (moduleName : String)
    (goals : Array (String × MVarId)) : MetaM (Except String (Json × Array String)) := do
  let before ← IO.getNumHeartbeats
  let saved : Meta.SavedState ← MonadBacktrack.saveState
  let outcome : Except String (Json × Array String) ←
    try
      pure (Except.ok (← withHeartbeatBudget (ExprGraphV3.buildGoalStateGraphNamedFullV3
        theoremName.toString (some moduleName) goals)))
    catch exception =>
      let message ← exception.toMessageData.toString
      pure (Except.error message)
  MonadBacktrack.restoreState saved
  IO.setNumHeartbeats before
  return outcome

/-- Instantiate metavariables before enumerating hypothesis-type positions; the
raw fallback is reported through the graph comparison, never silent. -/
def instantiateForLoci (e : Expr) : MetaM Expr := do
  try
    return (← Nazrin.instantiateAll e)
  catch _ =>
    return e

/-! ## Atomization replay -/

structure LoopResult where
  steps : Array Json := #[]
  stepCount : Nat := 0
  rejections : Nat := 0
  unmodeled : Nat := 0
  targetDropped : Nat := 0
  graphSteps : Nat := 0
  graphFailures : Nat := 0
  errorSteps : Nat := 0
  premiseSteps : Nat := 0
  premiseLabelInGraph : Nat := 0
  premiseLabelAppended : Nat := 0
  premiseLabelMissing : Nat := 0
  locusSteps : Nat := 0
  locusLabelled : Nat := 0
  locusErrors : Nat := 0
  coupledSteps : Nat := 0
  coupledEdges : Nat := 0
  graphNodes : Nat := 0
  graphBytes : Nat := 0
  failStage : Option String := none
  failMessage : String := ""

def ensureGoalId (pre : String) (ids : Array (MVarId × String)) (next : Nat)
    (goal : MVarId) : String × Nat × Array (MVarId × String) :=
  match ids.find? fun entry => entry.1 == goal with
  | some entry => (entry.2, next, ids)
  | none =>
    let id := s!"{pre}:g{next}"
    (id, next + 1, ids.push (goal, id))

def classifyMessage (message : String) : String :=
  if message.contains "timeout" then
    if message.contains "preprocessExpr" then "heartbeat.preprocessExpr"
    else if message.contains "whnf" then "heartbeat.whnf"
    else "heartbeat.other"
  else if message.contains "Dependent `Eq.rec" then "dependent_elim"
  else if message.contains "No apply holo-atomizer" then "no_atomizer_progress"
  else if message.contains "Could not make progress" then "no_atomizer_progress"
  else if message.contains "Tactic `" then "tactic_rejected"
  else if message.contains "not definitionally equal" then "reduction_mismatch"
  else if message.contains "type mismatch" then "type_mismatch"
  else if message.contains "No goals to be solved" then "no_goals"
  else if message.contains "Goal exhaustion" then "goal_exhaustion"
  else if message.contains "iteration limit" then "step_cap"
  else if message.contains "resume" then "resume"
  else "atomization_step"

/-- `goal_state`: every goal of the pre-step state, the current goal id and the
graph's coupled groups. -/
def goalStateJson (tables : GraphTables) (goalIds : Array String)
    (currentGoalId : String) : Json :=
  let currentRoot := tables.goals.findSome? fun row =>
    if row.goalId == currentGoalId then some row.root else none
  Json.mkObj [
    ("goal_ids", Json.arr (goalIds.map toJson)),
    ("goal_count", toJson goalIds.size),
    ("current_goal_id", toJson currentGoalId),
    ("current_goal_root", match currentRoot with | some r => toJson r | none => Json.null),
    ("goals", Json.arr (tables.goals.map fun row => Json.mkObj [
      ("goal_id", toJson row.goalId), ("root", toJson row.root),
      ("fvar_count", toJson row.fvarCount)])),
    ("coupled", Json.mkObj [
      ("goal_edges", Json.arr tables.goalEdges),
      ("groups", Json.arr tables.groups)])]

/-- Full schema-4 step record. -/
def stepRecord (runId pre moduleName : String) (envelopeSchema stepIndex : Nat)
    (goalId : String) (tacticJson : Json) (children : Array String)
    (extracted : Extracted) (fvarRows : Array FVarNodeRow) (premise : PremiseResult)
    (locus : LocusResult) (goalState : Json) (graphJson : Json) (tables : GraphTables)
    (graphBytes : Nat) : Json :=
  let graphProvenance := Json.mkObj [
    ("built", toJson true),
    ("source", toJson "pre_step_goal_state"),
    ("meta_state_discarded", toJson true),
    ("node_count", toJson tables.nodeCount),
    ("edge_count", toJson tables.edgeCount),
    ("goal_count", toJson tables.goals.size),
    ("fvar_count", toJson tables.fvars.size),
    ("constant_count", toJson tables.constants.size),
    ("locus_count", toJson tables.loci.size),
    ("coupled_group_count", toJson tables.groups.size),
    ("coupled_edge_count", toJson tables.goalEdges.size),
    ("bytes", toJson graphBytes),
    ("warnings", Json.arr (tables.warnings.map toJson))]
  let provenance := Json.mkObj [
    ("exporter", toJson "Standalone/StructuredTraceV4.lean"),
    ("schema_version", toJson schemaVersion),
    ("ok", toJson true),
    ("error", Json.null),
    ("graph", graphProvenance),
    ("premise", premise.json),
    ("locus", locus.json),
    ("target_reference_dropped", toJson extracted.targetDropped),
    ("rejected", toJson extracted.rejected.size)]
  Json.mkObj [
    ("schema", toJson envelopeSchema),
    ("schema_version", toJson schemaVersion),
    ("record", toJson "step"),
    ("run_id", toJson runId),
    ("theorem", toJson pre),
    ("module", toJson moduleName),
    ("step", toJson stepIndex),
    ("goal_id", toJson goalId),
    ("tactic", tacticJson),
    ("labels", Json.mkObj extracted.labels.toList),
    ("candidates", Json.mkObj [
      ("free_variables", toJson (fvarRows.map (·.name))),
      ("free_variable_count", toJson fvarRows.size),
      ("free_variable_nodes", Json.arr (fvarRows.map FVarNodeRow.json)),
      ("locus_candidates", Json.arr (locus.items.mapIdx LocusItem.json)),
      ("locus_count", toJson locus.items.size),
      ("locus_scope", toJson locus.scope),
      ("locus_fingerprint", toJson locus.fingerprint)]),
    ("premise_candidates", itemsJson premise.items),
    ("goal_state", goalState),
    ("goal_state_graph", graphJson),
    ("provenance", provenance),
    ("rejected", Json.arr (extracted.rejected.map rejectionJson)),
    ("children", Json.arr (children.map toJson))]

/-- Fail-closed record: no graph, no candidate table, no goal state, no label. -/
def errorRecord (runId pre moduleName : String) (envelopeSchema stepIndex : Nat)
    (goalId : String) (kind : String) (unmodeled : Bool) (children : Array String)
    (code message : String) : Json :=
  let error := Json.mkObj [("code", toJson code), ("message", toJson message)]
  Json.mkObj [
    ("schema", toJson envelopeSchema),
    ("schema_version", toJson schemaVersion),
    ("record", toJson "step"),
    ("run_id", toJson runId),
    ("theorem", toJson pre),
    ("module", toJson moduleName),
    ("step", toJson stepIndex),
    ("goal_id", toJson goalId),
    ("tactic", Json.mkObj [
      ("kind", toJson kind), ("parameters", Json.mkObj []),
      ("unmodeled", toJson unmodeled)]),
    ("error", error),
    ("provenance", Json.mkObj [
      ("exporter", toJson "Standalone/StructuredTraceV4.lean"),
      ("schema_version", toJson schemaVersion),
      ("ok", toJson false),
      ("error", error),
      ("graph", Json.mkObj [("built", toJson false)])]),
    ("children", Json.arr (children.map toJson))]

/-- Build the candidate table of the scope the tactic acted on, and check the
locus label against it.  Target scope reads the graph's `loci`; hypothesis scope
derives the type's positions and resolves their nodes in the graph. -/
def locusFor (graphJson : Json) (tables : GraphTables) (fvc : FVarCandidates)
    (fvarRows : Array FVarNodeRow) (lctx : LocalContext) (goalId : String)
    (tactic : AtomicTactic) (x : Extracted) :
    MetaM (Except String (LocusResult × Extracted)) := do
  match tactic with
  | .rewrite fvarId? pos _ _ _ =>
    match fvarId? with
    | none =>
      let locus := mkLocusResult (targetLocusItems tables goalId) "goal" none none
      return locus.withLabel x (locusPos pos) "payload_pos"
    | some id =>
      match fvc.index[id]?, (match fvc.index[id]? with
          | some i => fvarRows[i]?
          | none => none) with
      | some i, some row =>
        match lctx.find? id with
        | none =>
          return Except.error s!"site fvar {id.name} is not in the goal's local context"
        | some ldecl =>
          let type ← instantiateForLoci ldecl.type
          match hypothesisLocusItems (mkNodeWalk graphJson) row.typeNode type with
          | .ok items =>
            let locus := mkLocusResult items "hypotheses" (some fvc.names[i]!)
              (some row.graphIndex)
            return locus.withLabel x (locusPos pos) "payload_pos"
          | .error message => return Except.error message
      | _, _ =>
        return Except.error
          s!"site fvar {id.name} of goal {goalId} is not in the graph's fvar table"
  | .generalizeAt _ pos =>
    let locus := mkLocusResult (targetLocusItems tables goalId) "goal" none none
    return locus.withLabel x (locusPos pos) "payload_pos"
  | _ =>
    return Except.ok (mkLocusResult #[] "goal" none none, x)

/-- Replay atomization for one theorem.  Goal ordering, progress rule and resume
call are identical to `Standalone/StructuredTraceOne.lean` and `integratedAtomize`;
nothing about the atomizer is changed.  Every step is appended to `steps` as a
complete JSON object, so a mid-theorem failure still preserves the prefix. -/
def atomizationTrace (runId : String) (maxSteps : Nat) (envelopeSchema : Nat)
    (premiseMode : String) (thmName : Name) (moduleName : String) (info : ConstantInfo) :
    MetaM LoopResult := do
  let some value := info.value? | throwError "theorem has no proof value"
  let root := (← Meta.mkFreshExprSyntheticOpaqueMVar info.type).mvarId!
  let initialState ← Pantograph.GoalState.createFromMVars [root] root
  let atomizeM : Nazrin.Atomization.AtomizeT MetaM LoopResult := do
    let mut state := initialState
    let mut result : LoopResult := {}
    let mut goalIds : Array (MVarId × String) := #[]
    let mut nextGoal := 0
    let pre := thmName.toString
    let (_, nextGoal0, goalIds0) := ensureGoalId pre goalIds nextGoal root
    nextGoal := nextGoal0
    goalIds := goalIds0
    for _ in Array.range maxSteps do
      if state.goals.isEmpty then break
      state.restoreMetaM
      -- Stable ids for every goal of the pre-step state, and the display-name map
      -- the graph builder will use (same goal order, same LocalContexts).
      let mut pairs : Array (String × MVarId) := #[]
      let mut lctxs : Array LocalContext := #[]
      let mut stateGoalIds : Array String := #[]
      for goal in state.goals do
        let (id, ng, ids) := ensureGoalId pre goalIds nextGoal goal
        nextGoal := ng
        goalIds := ids
        pairs := pairs.push (id, goal)
        stateGoalIds := stateGoalIds.push id
        lctxs := lctxs.push (← goal.getDecl).lctx
      let displayNames := ExprGraphV2.displayNamesFor lctxs
      -- One graph per pre-step state.  Every goal attempt in this iteration sees
      -- the same state (a defer restores it), so the graph is shared by them.
      let graphStart ← IO.monoMsNow
      let graphOutcome ← buildGraphReadOnly thmName moduleName pairs
      let graphDone ← IO.monoMsNow
      debugLog s!"step {result.stepCount}: graph {graphDone - graphStart} ms, goals {pairs.size}"
      let (graphJson?, graphError?) : Option Json × Option String :=
        match graphOutcome with
        | .ok (json, _) => (some json, none)
        | .error message => (none, some message)
      let tables? : Option GraphTables := graphJson?.map parseGraphTables
      let solutionMap := (← get).solutionMap
      let goals := state.goalsArray.qsort fun g1 g2 =>
        let n1 := (solutionMap.get? g1).map fun { successors, .. } => successors.size
        let n2 := (solutionMap.get? g2).map fun { successors, .. } => successors.size
        n1.get! > n2.get!
      let mut progressed := false
      for goal in goals do
        state.restoreMetaM
        let decl ← goal.getDecl
        let goalId := (goalIds.find? (fun entry => entry.1 == goal)).map (·.2) |>.getD ""
        match ← Nazrin.Atomization.step' state goal with
        | .defer => continue
        | .failure message =>
          return { result with
            failStage := some (classifyMessage message)
            failMessage := message }
        | .next tactic nextState =>
          -- The graph and the display-name map were built from the pre-step state;
          -- restore it so the hypothesis type instantiated below matches the graph.
          state.restoreMetaM
          let mut childIds : Array String := #[]
          for child in nextState.goals do
            let (childId, ng2, ids2) := ensureGoalId pre goalIds nextGoal child
            nextGoal := ng2
            goalIds := ids2
            childIds := childIds.push childId
          let kind := AtomicTactic.kind tactic
          let unmodeled := (match tactic with
            | .define _ _ | .have _ _ | .let _ _ | .raw _ => true
            | _ => false)
          let locusBearing := (match tactic with
            | .rewrite .. | .generalizeAt .. => true
            | _ => false)
          let finish (code message : String) : LoopResult :=
            { result with
              errorSteps := result.errorSteps + 1
              graphFailures := result.graphFailures +
                (if code == "graph_build_failed" then 1 else 0)
              locusErrors := result.locusErrors + (if locusBearing then 1 else 0)
              steps := result.steps.push <|
                errorRecord runId pre moduleName envelopeSchema result.stepCount goalId
                  kind unmodeled childIds code message
              stepCount := result.stepCount + 1 }
          let mut outcome : LoopResult := result
          match graphJson?, tables? with
          | some graphJson, some tables =>
            match fvarTableFor tables.fvars displayNames goalId with
            | .error message =>
              outcome := finish "fvar_table_mismatch" message
            | .ok (fvc, fvarRows) =>
              let extracted := extract thmName fvc tactic
              let (extracted, premise) :=
                premiseTable tables.constants premiseMode extracted
              match ← locusFor graphJson tables fvc fvarRows decl.lctx goalId tactic
                  extracted with
              | .error message =>
                outcome := finish "locus_position_unresolved" message
              | .ok (locus, extracted) =>
                let tacticJson := Json.mkObj [
                  ("kind", toJson extracted.kind),
                  ("parameters", Json.mkObj extracted.params.toList),
                  ("unmodeled", toJson extracted.unmodeled)]
                let goalState := goalStateJson tables stateGoalIds goalId
                let graphBytes := graphJson.compress.length
                let record := stepRecord runId pre moduleName envelopeSchema
                  result.stepCount goalId tacticJson childIds extracted fvarRows premise
                  locus goalState graphJson tables graphBytes
                outcome := { result with
                  graphSteps := result.graphSteps + 1
                  graphNodes := result.graphNodes + tables.nodeCount
                  graphBytes := result.graphBytes + graphBytes
                  coupledSteps := result.coupledSteps +
                    (if tables.groups.size > 0 then 1 else 0)
                  coupledEdges := result.coupledEdges + tables.goalEdges.size
                  premiseSteps := result.premiseSteps +
                    (if premise.labelName.isSome then 1 else 0)
                  premiseLabelInGraph := result.premiseLabelInGraph +
                    (if premise.labelInGraph then 1 else 0)
                  premiseLabelAppended := result.premiseLabelAppended +
                    (if premise.appended then 1 else 0)
                  premiseLabelMissing := result.premiseLabelMissing +
                    (if premise.missing then 1 else 0)
                  locusSteps := result.locusSteps + (if locusBearing then 1 else 0)
                  locusLabelled := result.locusLabelled +
                    (if locus.labelIndex.isSome then 1 else 0)
                  rejections := result.rejections + extracted.rejected.size
                  unmodeled := result.unmodeled + (if extracted.unmodeled then 1 else 0)
                  targetDropped := result.targetDropped + extracted.targetDropped
                  steps := result.steps.push record
                  stepCount := result.stepCount + 1 }
          | _, none =>
            outcome := finish "graph_build_failed"
              (graphError?.getD "graph construction failed")
          | none, _ =>
            outcome := finish "graph_build_failed"
              (graphError?.getD "graph construction failed")
          result := outcome
          debugLog s!"step {result.stepCount - 1}: finish at {(← IO.monoMsNow) - graphDone} ms after graph"
          let remaining := nextState.goals ++ goals.toList.filter (· ≠ goal)
          match nextState.resume remaining with
          | .error _ =>
            return { result with
              failStage := some "resume"
              failMessage := "Could not resume atomization state" }
          | .ok resumed =>
            state := resumed
            progressed := true
            break
      if !progressed then
        return { result with
          failStage := some "goal_exhaustion"
          failMessage := s!"No goals ({state.goals.length}) in the active set can make progress" }
    if state.goals.isEmpty then
      return result
    else
      return { result with
        failStage := some "step_cap"
        failMessage := s!"{state.goals.length} goals left after {maxSteps}-step limit" }
  let rootState ← Nazrin.Atomization.createRootState root value
  atomizeM.run' rootState

/-! ## CLI -/

def usage : IO Unit := do
  IO.eprintln "Usage: lean --run Standalone/StructuredTraceV4.lean MODULE THEOREM OUTPUT_PATH"
  IO.eprintln "  Writes one schema-4 JSONL step record per step plus a final summary."
  IO.eprintln "  Env: NAZRIN_STRUCT_MAX_HEARTBEATS (default 200000),"
  IO.eprintln "       NAZRIN_STRUCT_MAX_STEPS (default 3000),"
  IO.eprintln "       NAZRIN_STRUCT_RUN_ID, NAZRIN_STRUCT_STEP_SCHEMA (3|4),"
  IO.eprintln "       NAZRIN_STRUCT_PREMISE_MODE (graph|append)."

def toolchainString : IO String := do
  if ← System.FilePath.pathExists "lean-toolchain" then
    return (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  else
    return Lean.versionString

def writeLines (path : System.FilePath) (values : Array Json) : IO Unit := do
  IO.FS.withFile path .write fun handle => do
    for value in values do
      handle.putStrLn value.compress

def summary (runId moduleName thmName status stage message : String)
    (envelopeSchema : Nat) (premiseMode : String) (loop : LoopResult)
    (maxHeartbeats maxSteps : Nat) (toolchain : String) (elapsedMs : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson envelopeSchema),
    ("schema_version", toJson schemaVersion),
    ("record", toJson "theorem"),
    ("run_id", toJson runId),
    ("theorem", toJson thmName),
    ("module", toJson moduleName),
    ("status", toJson status),
    ("stage", toJson stage),
    ("message", toJson message),
    ("steps", toJson loop.stepCount),
    ("label_rejections", toJson loop.rejections),
    ("unmodeled_steps", toJson loop.unmodeled),
    ("schema4", Json.mkObj [
      ("premise_mode", toJson premiseMode),
      ("graph_steps", toJson loop.graphSteps),
      ("graph_failures", toJson loop.graphFailures),
      ("graph_error_steps", toJson loop.errorSteps),
      ("premise_steps", toJson loop.premiseSteps),
      ("premise_label_in_graph", toJson loop.premiseLabelInGraph),
      ("premise_label_appended", toJson loop.premiseLabelAppended),
      ("premise_label_missing", toJson loop.premiseLabelMissing),
      ("locus_steps", toJson loop.locusSteps),
      ("locus_labelled_steps", toJson loop.locusLabelled),
      ("locus_error_steps", toJson loop.locusErrors),
      ("coupled_steps", toJson loop.coupledSteps),
      ("coupled_edges", toJson loop.coupledEdges),
      ("graph_nodes_total", toJson loop.graphNodes),
      ("graph_bytes_total", toJson loop.graphBytes),
      ("target_leakage_dropped", toJson loop.targetDropped)]),
    ("max_heartbeats", toJson maxHeartbeats),
    ("max_steps", toJson maxSteps),
    ("toolchain", toJson toolchain),
    ("exporter", toJson "Standalone/StructuredTraceV4.lean"),
    ("elapsed_ms", toJson elapsedMs)]

def main (args : List String) : IO UInt32 := do
  let (moduleName, thmName, outputPath) ← match args with
    | [m, t, o] => pure (m, t, o)
    | _ => usage; return 1
  let maxHeartbeats ← natEnv "NAZRIN_STRUCT_MAX_HEARTBEATS" 200000
  let maxSteps ← natEnv "NAZRIN_STRUCT_MAX_STEPS" 3000
  let runId ← strEnv "NAZRIN_STRUCT_RUN_ID" "local"
  let envelopeSchema ← do
    let raw ← strEnv "NAZRIN_STRUCT_STEP_SCHEMA" "3"
    match raw.toNat? with
    | some 4 => pure 4
    | _ => pure 3
  let premiseMode ← do
    let raw ← strEnv "NAZRIN_STRUCT_PREMISE_MODE" "graph"
    if raw == "graph" || raw == "append" then pure raw else pure "graph"
  -- Accepted for Gate 1.2 compatibility; schema 4 always emits full loci.
  let _ ← strEnv "NAZRIN_STRUCT_EMIT_LOCI" "0"
  let toolchain ← toolchainString
  let started ← IO.monoMsNow
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  unsafe Pantograph.initSearch ""
  let env ← Lean.importModules #[{ module := moduleName.toName }] {} 1 (loadExts := true)
  let fail (stage message : String) : IO UInt32 := do
    let now ← IO.monoMsNow
    writeLines outputPath #[summary runId moduleName thmName "failure" stage message
      envelopeSchema premiseMode {} maxHeartbeats maxSteps toolchain (now - started)]
    IO.eprintln s!"StructuredTraceV4: {thmName}: {stage}: {message}"
    return 2
  let some info := env.find? thmName.toName
    | return ← fail "lookup" "unknown constant in imported module"
  unless info matches .thmInfo .. do
    return ← fail "not_theorem" "constant is not a theorem"
  let coreContext ← Pantograph.createCoreContext #[s!"maxHeartbeats={maxHeartbeats}"]
  let outcome ←
    try
      match ← (Lean.Meta.MetaM.run' (atomizationTrace runId maxSteps envelopeSchema
          premiseMode thmName.toName moduleName info)).run coreContext { env := env } |>.toBaseIO with
      | .ok (loop, _) => pure (Except.ok loop)
      | .error exception =>
        let message ← exception.toMessageData.toString
        pure (Except.error (classifyMessage message, message))
    catch exception =>
      let message := toString exception
      pure (Except.error (classifyMessage message, message))
  let now ← IO.monoMsNow
  let elapsed := now - started
  match outcome with
  | .ok loop =>
    writeLines outputPath (loop.steps.push <|
      summary runId moduleName thmName
        (if loop.failStage.isSome then "failure" else "success")
        (loop.failStage.getD "ok") loop.failMessage
        envelopeSchema premiseMode loop maxHeartbeats maxSteps toolchain elapsed)
    if loop.failStage.isSome then
      IO.eprintln s!"StructuredTraceV4: {thmName}: {loop.failStage.getD "?"}: partial {loop.stepCount} step(s)"
      return 2
    else
      return 0
  | .error (stage, message) =>
    writeLines outputPath #[summary runId moduleName thmName "failure" stage message
      envelopeSchema premiseMode {} maxHeartbeats maxSteps toolchain elapsed]
    IO.eprintln s!"StructuredTraceV4: {thmName}: {stage}: {message}"
    return 2

end StructuredTraceV4

def main (args : List String) : IO UInt32 :=
  StructuredTraceV4.main args