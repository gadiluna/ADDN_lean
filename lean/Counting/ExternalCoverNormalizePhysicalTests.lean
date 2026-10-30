import Counting.ExternalCoverNormalizeMachine
import Counting.MachineTestMemo

namespace Counting.External.CoverNormalization.PhysicalTests
open Machine
private def checked (program : Program) (word : List Bool) : IO Unit := do
  let expected:=normalizeWord word
  match TestMemo.finishWithin program 20000000 0 (TestMemo.empty program) (initial program word) with
  | none=>throw (IO.userError "normalization physical transducer exceeded fuel")
  | some (steps,finish)=>
    let right:=finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "normalization physical transducer has wrong output or dirty work tape")
    IO.println s!"X3C normalization physical run: {steps} transitions, exact clean output."
def tests : IO Unit := do
  let program:=machineGenerator
  checked program []
  checked program (X3CEncoding.rawCodec.encode ([],[]))
  checked program (X3CEncoding.rawCodec.encode (List.replicate 3 true,[[0,1,2]]))
#eval tests
end Counting.External.CoverNormalization.PhysicalTests
