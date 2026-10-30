import Counting.ExternalMatchingMachine
import Counting.MachineTestMemo

namespace Counting.External.MatchingMachine.PhysicalTests
open Machine
private def checked (program : Program) (input : List Bool) : IO Unit := do
  let expected := reduceMatching input
  match TestMemo.finishWithin program 20000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "three-SAT-to-matching physical test exceeded fuel")
  | some (steps,finish) =>
    let right := finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "three-SAT-to-matching physical output differs or has dirty work tape")
    IO.println s!"Three-SAT-to-matching physical run: {steps} transitions; exact clean output."
def tests : IO Unit := do
  let program := machineGenerator
  checked program []
  checked program (CNFEncoding.rawCodec.encode ([],[]))
  checked program (CNFEncoding.rawCodec.encode ([true],[]))
#eval tests
end Counting.External.MatchingMachine.PhysicalTests
