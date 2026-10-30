import Counting.MachineAuditPostSolver
import Counting.MachineTestMemo

namespace Counting.Machine.AuditPostSolverTests
open StackMachine.AuditPostSolver

def tests : IO Unit := do
  let p:=auditPostSolverProgram
  let vista : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩],0⟩
  let input:=inputWord vista 1 0 none
  let output:=outputWord vista 1 0 none
  match TestMemo.finishWithin p 5000000 0 (TestMemo.empty p) (initial p input) with
  | none=>throw (IO.userError "Physical post-solver composition exhausted regression fuel")
  | some (steps,last)=>
    let right:=last.tape.head::last.tape.right
    unless last.tape.left.all (· == .blank) && right.take output.length==output.map bitSymbol &&
        (right.drop output.length).all (· == .blank) do
      throw (IO.userError "Physical post-solver optional result or full-tape cleanup mismatch")
    IO.println s!"Post-solver missing-solution branch: {steps} actual physical transitions, entire tape clean."

#eval tests
end Counting.Machine.AuditPostSolverTests
