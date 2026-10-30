import Counting.StackRealizabilityVistaMachine
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.VistaComplement.Tests

private def requireRun (name : String) (input : List Bool) (expected : Bool) : IO Nat := do
  unless predicate input==expected do
    throw (IO.userError s!"Complement specification disagrees with known case: {name}")
  let program := verifier.program
  match TestLazy.finishWithin program 8000000 0 (TestLazy.empty program) (initial program input) with
  | none => throw (IO.userError s!"Complete complement verifier exhausted fuel: {name}")
  | some (time,result) =>
    unless result.store 1==[expected] do
      throw (IO.userError s!"Complete complement verifier returned an incorrect answer: {name}")
    return time

/-- Two focused end-to-end cases exercise the malformed branch and both
accepted certificate calls. The component suite covers replacement and
same-order rejection separately. -/
def tests : IO Unit := do
  let root : Executable.Node := ⟨0,none,true,0,[]⟩
  let vista : Executable.Vista := ⟨#[root],0⟩
  let input := Encoding.vistaInput.encode (vista,1)
  let witness := Encoding.twoOrderWitness.encode ((1,[1]),(2,[1]))
  let cases := [("malformed framing",[],false),
    ("two distinct realized orders",Encoding.pairWords input witness,true)]
  let mut maximum := 0
  for (name,word,expected) in cases do
    let time ← requireRun name word expected
    maximum := max maximum time
  IO.println s!"Vista complement verifier passed {cases.length} end-to-end cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.VistaComplement.Tests
