import Counting.MachineAuditCandidate
import Counting.StackMachineTestLazy

namespace Counting.Machine.AuditCandidateTests

def tests : IO Unit := do
  let p:=StackMachine.AuditCandidate.complete.program
  let cases : List (Option (Array Rat) × Nat × Option (Array Nat)) :=
    [(none,0,none),(some #[],0,some #[]),(some #[],1,none),(some #[1,3],4,some #[1,3]),
      (some #[1,3],3,none),(some #[0,2],2,none),(some #[-1,2],1,none),(some #[(3:Rat)/2],1,none)]
  for (values,candidate,expected) in cases do
    let input:=StackMachine.AuditCandidate.inputWord values candidate
    let output:=(Encoding.optional (Encoding.array Encoding.natural)).encode expected
    match StackMachine.TestLazy.finishWithin p 1000000 0 (StackMachine.TestLazy.empty p)
        (StackMachine.initial p input) with
    | none=>throw (IO.userError "Composed positive/sum check exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all
          (fun r=>last.store r==if r.val=1 then output else []) do
        throw (IO.userError "Composed positive/sum result or cleanup mismatch")
      IO.println s!"Candidate {candidate}, solver result {repr values}: {steps} transitions, all registers checked."
  IO.println "Eight composed optional/positive/sum regressions passed."

#eval tests
end Counting.Machine.AuditCandidateTests
