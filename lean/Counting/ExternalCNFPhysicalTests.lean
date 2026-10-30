import Counting.ExternalCNFMachine
import Counting.MachineTestMemo

namespace Counting.External.CNFMachine.PhysicalTests
open Machine

private def checked (program : Program) (input : List Bool) : IO Unit := do
  let expected := reduceThreeSAT input
  match TestMemo.finishWithin program 10000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "SAT-to-three-SAT physical test exceeded fuel")
  | some (steps,finish) =>
    let right := finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "SAT-to-three-SAT physical output differs or has dirty work tape")
    IO.println s!"SAT-to-three-SAT physical run: {steps} transitions; exact clean output."

def tests : IO Unit := do
  let program := machineGenerator
  checked program []
  checked program (CNFEncoding.rawCodec.encode ([],[]))
  checked program (CNFEncoding.rawCodec.encode ([],[[]]))

#eval tests
end Counting.External.CNFMachine.PhysicalTests
