import Counting.MachineAuditPrefix
import Counting.MachineTestMemo

namespace Counting.Machine.AuditPrefixTests
open StackMachine.AuditPrefix

def tests : IO Unit := do
  let p:=auditPrefixProgram
  let vista : Executable.Vista:=⟨#[],0⟩
  let input:=inputWord vista 1 1 1
  let output:=Encoding.optionalNatural.encode (Executable.auditPrefix? vista 1 1 1)
  match TestMemo.finishWithin p 10000000 0 (TestMemo.empty p) (initial p input) with
  | none=>throw (IO.userError "Physical prefix regression exhausted fuel")
  | some (steps,finish)=>
    let right:=finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take output.length==output.map bitSymbol &&
        (right.drop output.length).all (· == .blank) do
      throw (IO.userError "Physical prefix answer or tape cleanup mismatch")
    IO.println s!"Complete physical prefix: {steps} TM transitions; rejected malformed vista, entire tape clean."

#eval tests
end Counting.Machine.AuditPrefixTests
