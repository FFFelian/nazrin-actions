import Standalone.AtomizerCore

open Lean Nazrin

private def protocolPrefix := "NAZRIN_WORKER "

private def reply (json : Json) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn (protocolPrefix ++ json.compress)
  stdout.flush

private def failureMessage (exception : Exception) : IO String := do
  try
    return (← exception.toMessageData.toString).take 16384 |>.toString
  catch _ =>
    return "Internal exception (message formatting failed)"

/-- One imported module, one symbol at a time. The supervisor enforces hard deadlines. -/
def main (args : List String) : IO UInt32 := do
  let [moduleName, heartbeatLimit] := args
    | do
      IO.eprintln "Usage: AtomizerWorker MODULE MAX_HEARTBEATS"
      return 1
  unsafe Pantograph.initSearch ""
  let env ← Lean.importModules #[{ module := moduleName.toName }] {} 1 (loadExts := true)
  -- Resolve against actual environment Names, including numeric/private components.
  let names : Std.HashMap String Name := env.constants.fold (init := {}) fun names name _ =>
    names.insert name.toString name
  let coreContext ← Pantograph.createCoreContext #[s!"maxHeartbeats={heartbeatLimit}"]
  reply <| Json.mkObj [("status", toJson "ready"), ("module", toJson moduleName)]
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then
      break
    let request := do
      let json ← Json.parse line
      let symbol ← json.getObjValAs? String "theorem"
      let path ← json.getObjValAs? String "path"
      return (symbol, path)
    let .ok (symbol, path) := request
      | do
        reply <| Json.mkObj [("status", toJson "invalid_request")]
        continue
    let some name := names[symbol]?
      | do
        reply <| Json.mkObj [("status", toJson "invalid_symbol"), ("theorem", toJson symbol)]
        continue
    let coreM : CoreM (Array String) := withAtLeastMaxRecDepth 8192 $ withCurrHeartbeats do
      let some decl := env.find? name | throwError "Could not find symbol"
      unless decl matches .thmInfo .. do throwError "Declaration is not a theorem"
      let some val := decl.value? | throwError "Theorem has no proof value"
      (integratedAtomize decl.type val).run'
    let started ← IO.monoMsNow
    let result ← (coreM.run coreContext { env }).toBaseIO
    let elapsed := (← IO.monoMsNow) - started
    -- Keep result writes outside the exhausted CoreM/heartbeat context.
    match result with
    | .ok (steps, _) =>
      IO.FS.withFile path .write fun handle => do
        for step in steps do handle.putStrLn step
        handle.flush
      reply <| Json.mkObj [
        ("status", toJson "success"), ("theorem", toJson symbol),
        ("elapsed_ms", toJson elapsed), ("steps", toJson steps.size)]
    | .error exception =>
      let message ← failureMessage exception
      IO.FS.writeFile (path ++ ".log") message
      reply <| Json.mkObj [
        ("status", toJson "failure"), ("theorem", toJson symbol),
        ("elapsed_ms", toJson elapsed)]
  return 0
