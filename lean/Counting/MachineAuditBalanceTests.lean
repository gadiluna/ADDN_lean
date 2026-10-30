import Counting.MachineAuditBalance
import Counting.MachineTestMemo

namespace Counting.Machine.AuditBalanceTests
open StackMachine.AuditBalance

def tests : IO Unit := do
  let p:=auditBalanceProgram
  let vista : Executable.Vista:=⟨#[],0⟩
  let input:=balanceInputWord 0 vista #[]
  let output:=Encoding.boolean.encode (Executable.auditBalance vista #[] 0)
  match TestMemo.finishWithin p 5000000 0 (TestMemo.empty p) (initial p input) with
  | none=>throw (IO.userError "Physical balance check exhausted regression fuel")
  | some (steps,last)=>
    let right:=last.tape.head::last.tape.right
    unless last.tape.left.all (· == .blank) && right.take output.length==output.map bitSymbol &&
        (right.drop output.length).all (· == .blank) do
      throw (IO.userError "Physical balance decision or full-tape cleanup mismatch")
    IO.println s!"Empty-DAG balance: {steps} actual physical transitions, entire tape clean."

#eval tests
end Counting.Machine.AuditBalanceTests
