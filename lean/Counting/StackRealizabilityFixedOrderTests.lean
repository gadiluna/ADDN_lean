import Counting.StackRealizabilityFixedOrderMachine
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.FixedOrderRecognition.Tests

private def requireRun (name : String) (input : List Bool) (expected : Bool) : IO Nat := do
  unless predicate input==expected do
    throw (IO.userError s!"Fixed-order specification disagrees with known case: {name}")
  let program := verifier.program
  match TestLazy.finishWithin program 8000000 0 (TestLazy.empty program) (initial program input) with
  | none => throw (IO.userError s!"Fixed-order verifier exhausted fuel: {name}")
  | some (time,result) =>
    unless result.store 1==[expected] do
      throw (IO.userError s!"Fixed-order verifier returned an incorrect answer: {name}")
    return time

def tests : IO Unit := do
  let root : Executable.Node := ⟨0,none,true,0,[]⟩
  let vista : Executable.Vista := ⟨#[root],0⟩
  let input := Encoding.fixedOrderInput.encode (vista,1,1)
  let witness := (Encoding.list Encoding.natural).encode [1]
  let cases := [("malformed framing",[],false),
    ("singleton fixed order",Encoding.pairWords input witness,true)]
  let mut maximum := 0
  for (name,word,expected) in cases do
    let time ← requireRun name word expected
    maximum := max maximum time
  IO.println s!"Fixed-order verifier passed {cases.length} end-to-end cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.FixedOrderRecognition.Tests
