import Nazrin.Atomization
import Pantograph

open Lean Nazrin

deriving instance DecidableEq, Repr for MVarId

open Pantograph Atomization in
def integratedAtomize (t e : Expr) : MetaM (Array String) := do
  let root := (← Meta.mkFreshExprSyntheticOpaqueMVar t).mvarId!
  let state ← GoalState.createFromMVars [root] root
  let atomizeM : AtomizeT CoreM _ := do
    let mut result := #[]
    let mut state := state
    let iterations := 1000
    for _i in Array.range iterations do
      if state.goals.isEmpty then
        break
      let solutionMap := (← get).solutionMap
      let goals := state.goalsArray.qsort fun g1 g2 =>
        let n1 := (solutionMap.get? g1).map fun { successors, .. } => successors.size
        let n2 := (solutionMap.get? g2).map fun { successors, .. } => successors.size
        n1.get! > n2.get!
      let mut progressed := false
      for goal in goals do
        match ← Atomization.step state goal with
        | .defer => continue
        | .failure message => throwError s!"Atomization failed: {message}"
        | .next tactic nextState =>
          let nextStateGoals := ",".intercalate (nextState.goals.map (·.name.toString))
          result := result.push s!"{goal.name}\t{tactic}\t{nextStateGoals}"
          let .ok nextState := nextState.resume (nextState.goals ++ goals.toList.filter (· ≠ goal))
            | throwError "Could not resume"
          state := nextState
          progressed := true
          break
      if !progressed then
        throwError s!"Goal exhaustion. No goals ({state.goals.length}) in the active set can make progress"
    unless state.goals.isEmpty do
      throwError "{state.goals.length} goals left after iteration limit"
    return (state, result)
  let rootState ← createRootState root e
  let (_, result) ← show CoreM _ from atomizeM.run' rootState
  return result
