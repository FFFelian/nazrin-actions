import Nazrin.Essentialization

open Lean Nazrin

/-- Export the same eligible theorem universe used by Atomizer, with provenance. -/
def main (args : List String) : IO UInt32 := do
  let [output, module] := args
    | do
      IO.eprintln "Usage: lean --run Standalone/Inventory.lean OUTPUT_TSV MODULE"
      return 1
  unsafe Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := module.toName }] {} 1 (loadExts := true)
  let names := env.constants.fold (init := []) fun acc name info =>
    if !isMatcher env name && !isNameInternal name && (info matches .thmInfo ..) then
      name :: acc
    else acc
  let mathlib ← IO.FS.withFile output .write fun handle => do
    let mut mathlib := 0
    handle.putStrLn "index\ttheorem\tmodule"
    for (name, index) in names.zipIdx do
      let owner := match env.getModuleIdxFor? name with
        | some idx => env.header.moduleNames[idx.toNat]!.toString
        | none => "<unknown>"
      if owner == "Mathlib" || owner.startsWith "Mathlib." then
        mathlib := mathlib + 1
      handle.putStrLn s!"{index}\t{name}\t{owner}"
    return mathlib
  IO.println s!"Eligible theorems: {names.length}; owned by Mathlib: {mathlib}; imported dependencies: {names.length - mathlib}"
  IO.println s!"Two shard sizes: {(names.length + 1) / 2}, {names.length / 2}"
  return 0
