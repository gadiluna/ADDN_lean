import Counting.InputMultisetDag
import Counting.InputMultisetDagRecovery

/-! Direct executable regression checks on compressed input vistas. The test
harness supplies identities only to construct network communication; neither
recovery nor the DAG updater receives them. These are evaluations, not axioms. -/
namespace Counting.InputMultiset.DagTests
open Executable

private def require (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Input-multiset DAG test failed: {name}")

/-- Directed spanning cycle, optionally with large parallel loops. -/
def multiplicity (n round loops source target : Nat) : Nat :=
  (if n > 1 && target == (source + 1) % n then 1 + round % 3 else 0) +
  (if target == source then loops else 0)

def networkRound (round loops : Nat) (states : Array Vista) : Option (Array Vista) := do
  let updated ← (List.range states.size).mapM fun receiver => do
    let old := states[receiver]?.getD default
    let messages := (List.range states.size).filterMap fun sender =>
      let count := multiplicity states.size round loops sender receiver
      if count == 0 then none else some (states[sender]?.getD default, count)
    let degree := ((List.range states.size).map
      (multiplicity states.size round loops receiver)).sum
    updateVista? old messages degree
  return updated.toArray

def runCase (name : String) (inputs : List Nat) (leaders loops : Nat) : IO Unit := do
  let mut states := ((inputs.zipIdx).map fun (input, i) => Dag.initial id (i < leaders) input).toArray
  require (name ++ ": initial compressed vistas valid") (states.all (·.valid))
  let bound := 2 * inputs.length - 2
  for round in List.range bound do
    let some next := networkRound (round + 1) loops states
      | throw (IO.userError s!"{name}: DAG update rejected round {round + 1}")
    require (name ++ ": valid updated vistas") (next.all (·.valid))
    states := next
  let answer : Multiset Nat := inputs
  require (name ++ ": exact multiset at 2n−2")
    (states.all fun vista => decide (DagRecovery.recover inputs.length vista id = some answer))
  let some after := networkRound (bound + 1) loops states
    | throw (IO.userError s!"{name}: extra DAG update failed")
  require (name ++ ": recovery stays exact later")
    (after.all fun vista => decide (DagRecovery.recover inputs.length vista id = some answer))

def tests : IO Unit := do
  runCase "singleton, no arcs" [17] 1 0
  runCase "singleton, huge loops" [23] 1 (2 ^ 128)
  runCase "two distinct inputs, one leader" [7, 9] 1 0
  runCase "two equal inputs, all leaders" [7, 7] 2 2
  runCase "three agents, repeated input" [7, 9, 7] 1 0
  runCase "three distinct inputs, all leaders" [7, 9, 11] 3 0
  runCase "four agents, two leaders, huge loops" [1, 1, 2, 3] 2 (2 ^ 128)
  IO.println "Input-multiset compressed-DAG tests passed: 7 cases, each at the bound and one round later."

#eval tests

end Counting.InputMultiset.DagTests
