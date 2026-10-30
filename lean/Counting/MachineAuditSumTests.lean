import Counting.MachineAuditSum
import Counting.StackMachineTestLazy

namespace Counting.Machine.AuditSumTests

def tests : IO Unit := do
  let p:=StackMachine.AuditSum.complete.program
  for (values,candidate,expected) in [([],0,true),([],1,false),([1,2,3],6,true),([1,2,3],5,false),
      ([0,2],2,false),([1,128,257],386,true)] do
    let input:=StackMachine.AuditSum.inputWord values candidate
    match StackMachine.TestLazy.finishWithin p 1000000 0 (StackMachine.TestLazy.empty p)
        (StackMachine.initial p input) with
    | none=>throw (IO.userError "Candidate sum exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all
          (fun r=>last.store r==if r.val=1 then [expected] else []) do
        throw (IO.userError "Candidate sum result or cleanup mismatch")
      IO.println s!"Candidate {candidate}, values {values}: {steps} transitions, all registers checked."
  IO.println "Six candidate-sum regressions passed."

#eval tests
end Counting.Machine.AuditSumTests
