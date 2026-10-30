import Counting.MachineAuditPositive
import Counting.StackMachineTestLazy

namespace Counting.Machine.AuditPositiveTests

def check (program : StackMachine.Program) (values : Option (Array Rat))
    (expected : Option (Array Nat)) (label : String) : IO Unit := do
  let input:=StackMachine.AuditPositive.inputWord values
  let expectedWord:=(Encoding.optional (Encoding.array Encoding.natural)).encode expected
  match StackMachine.TestLazy.finishWithin program 1000000 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none=>throw (IO.userError s!"Optional positive conversion exhausted fuel: {label}")
  | some (steps,last)=>
    unless (List.finRange (program.extraRegisters+2)).all
        (fun r=>last.store r == if r.val=1 then expectedWord else []) do
      throw (IO.userError s!"Optional positive conversion output/cleanup mismatch: {label}")
    IO.println s!"{label}: {steps} actual stack transitions; all registers checked."

def tests : IO Unit := do
  let program:=StackMachine.AuditPositive.routine.program
  check program none none "No solver result"
  check program (some #[]) (some #[]) "Empty vector"
  check program (some #[1,3,129]) (some #[1,3,129]) "Positive integral values"
  check program (some #[1,0]) none "Zero entry"
  check program (some #[-1,2]) none "Negative entry"
  check program (some #[(3:Rat)/2,2]) none "Fractional entry"
  IO.println "Six optional positive-conversion regressions passed."

#eval tests
end Counting.Machine.AuditPositiveTests
