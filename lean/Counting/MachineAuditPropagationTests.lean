import Counting.MachineAuditPropagation
import Counting.MachineTestMemo

namespace Counting.Machine.AuditPropagationTests
open StackMachine.AuditPropagation

def tests : IO Unit := do
  let p:=auditPropagationProgram
  let vista : Executable.Vista:=⟨#[],0⟩
  let input:=propagationInputWord 0 vista #[]
  let output:=propagationOutputWord 0 vista #[]
  match TestMemo.finishWithin p 5000000 0 (TestMemo.empty p) (initial p input) with
  | none=>throw (IO.userError "Physical propagation exhausted regression fuel")
  | some (steps,last)=>
    let right:=last.tape.head::last.tape.right
    unless last.tape.left.all (· == .blank) && right.take output.length==output.map bitSymbol &&
        (right.drop output.length).all (· == .blank) do
      throw (IO.userError "Physical propagation output or full tape cleanup mismatch")
    IO.println s!"Empty-DAG propagation: {steps} actual physical transitions, entire tape clean."

#eval tests
end Counting.Machine.AuditPropagationTests
