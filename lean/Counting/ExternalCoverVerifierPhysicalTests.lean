import Counting.ExternalCoverVerifierMachine
import Counting.MachineTestMemo

namespace Counting.External.CoverVerification.PhysicalTests
open Machine
private def checked (program : Program) (word : List Bool) : IO Unit := do
  let expected := [verify word]
  match TestMemo.finishWithin program 20000000 0 (TestMemo.empty program) (initial program word) with
  | none => throw (IO.userError "X3C physical verifier exceeded fuel")
  | some (steps,finish) =>
    let right := finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "X3C physical verifier has wrong output or dirty work tape")
    IO.println s!"X3C verifier physical run: {steps} transitions, exact clean output."
def tests : IO Unit := do
  let program := transducer
  checked program []
  checked program (Encoding.pairWords (X3CEncoding.rawCodec.encode ([],[])) [])
  checked program (Encoding.pairWords (X3CEncoding.rawCodec.encode (List.replicate 3 true,[])) [])
  checked program (Encoding.pairWords (X3CEncoding.rawCodec.encode (List.replicate 3 true,[[0,1,2]])) [true])
#eval tests
end Counting.External.CoverVerification.PhysicalTests
