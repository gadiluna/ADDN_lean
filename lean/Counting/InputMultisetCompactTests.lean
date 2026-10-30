import Counting.InputMultisetCompactCorrectness

/-! Full local binary-packet executions, including the interval between
Counting termination and later multiset termination in all-leader networks. -/
namespace Counting.InputMultiset.CompactTests
open Executable

private def require (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Input-multiset compact test failed: {name}")

def multiplicity (n round loops source target : Nat) : Nat :=
  (if n > 1 && target == (source + 1) % n then 1 + round % 3 else 0) +
  (if target == source then loops else 0)

def compactRound (round loops : Nat) (states : Array (Compact.State Nat)) :
    Option (Array (Compact.State Nat)) := do
  let updated ← (List.range states.size).mapM fun receiver => do
    let some old := states[receiver]? | none
    let messages := (List.range states.size).filterMap fun sender => do
      let count := multiplicity states.size round loops sender receiver
      if count == 0 then none else do
        let state ← states[sender]?
        let packet ← Compact.message state
        return (packet, count)
    let degree := ((List.range states.size).map
      (multiplicity states.size round loops receiver)).sum
    Compact.step old messages degree
  return updated.toArray

def runCompactCase (name : String) (inputs : List Nat) (leaders loops : Nat) : IO Unit := do
  let mut states := ((inputs.zipIdx).map fun (input, i) =>
    Compact.initial Encodable.encode leaders (i < leaders) input).toArray
  let bound := terminationTime inputs.length leaders
  for round in List.range bound do
    require (name ++ ": no early outer decision") (states.all fun state => state.output.isNone)
    let some next := compactRound (round + 1) loops states
      | throw (IO.userError s!"{name}: compact update rejected round {round + 1}")
    require (name ++ ": valid input DAG") (next.all fun state => state.vista.valid)
    states := next
  let answer : Multiset Nat := inputs
  require (name ++ ": exact simultaneous multiset")
    (states.all fun state => decide (state.output = some answer))
  require (name ++ ": complete silence") (states.all fun state => (Compact.message state).isNone)
  let some after := compactRound (bound + 1) loops states
    | throw (IO.userError s!"{name}: compact halted update failed")
  require (name ++ ": frozen after termination")
    ((states.zip after).all fun pair => pair.1.vista == pair.2.vista &&
      pair.1.counting == pair.2.counting && decide (pair.1.output = pair.2.output))

def tests : IO Unit := do
  runCompactCase "compact singleton, no arcs" [17] 1 0
  runCompactCase "compact singleton, huge loops" [23] 1 (2 ^ 128)
  runCompactCase "compact two agents, one leader" [7, 9] 1 0
  runCompactCase "compact two agents, all leaders" [7, 9] 2 2
  runCompactCase "compact three agents, two leaders" [7, 9, 7] 2 3
  runCompactCase "compact all leaders, delayed input stop" [1, 2, 3, 4] 4 0
  runCompactCase "compact all leaders, constant input" [11, 11, 11, 11] 4 1
  IO.println "Input-multiset compact protocol tests passed: 7 complete executions, exact termination, freezing, and silence."

#eval tests

end Counting.InputMultiset.CompactTests
