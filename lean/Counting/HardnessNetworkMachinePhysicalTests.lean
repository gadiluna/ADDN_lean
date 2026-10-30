import Counting.HardnessNetworkMachineMachine
import Counting.MachineTestMemo

namespace Counting.HardnessNetworkMachine.PhysicalTests
open Machine

private def checked (program : Program) (word : List Bool) : IO Unit := do
  let expected:=networkTransform word
  match TestMemo.finishWithin program 100000000 0 (TestMemo.empty program) (initial program word) with
  | none=>throw (IO.userError "physical hardness network generator exceeded fuel")
  | some (steps,finish)=>
    let right:=finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "physical network generator has wrong output or dirty work tape")
    IO.println s!"Hardness network physical generator: {steps} transitions, exact clean output."

def tests : IO Unit := do
  let program:=networkMachine
  checked program []
  checked program (X3CEncoding.rawCodec.encode ([],[]))

#eval tests
end Counting.HardnessNetworkMachine.PhysicalTests
