import Counting.MachineAuditDescendant
import Counting.MachineTestMemo

namespace Counting.Machine.AuditDescendantTests
open StackMachine.AuditDescendant

def tests : IO Unit := do
  let p:=auditDescendantProgram
  let vista : Executable.Vista:=⟨#[],0⟩
  let input:=completeInputWord vista #[] 0 0
  let output:=[Executable.auditDescendants vista #[] 0 0]
  match TestMemo.finishWithin p 10000000 0 (TestMemo.empty p) (initial p input) with
  | none=>throw (IO.userError "Physical descendant regression exhausted fuel")
  | some (steps,finish)=>
    let right:=finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take output.length==output.map bitSymbol &&
        (right.drop output.length).all (· == .blank) do
      throw (IO.userError "Physical descendant answer or tape cleanup mismatch")
    IO.println s!"Complete physical descendant: {steps} TM transitions; empty view accepted, entire tape clean."

#eval tests
end Counting.Machine.AuditDescendantTests
