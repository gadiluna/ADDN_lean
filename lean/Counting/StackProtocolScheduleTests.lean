import Counting.MachineProtocolSchedule
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.ProtocolSchedule.Tests

def tests : IO Unit := do
  let program:=complete.program
  let cases : List (Nat×Nat):=
    [(0,0),(0,9),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),
     (2,2),(2,3),(2,4),(2,5),(3,4),(3,5),(3,6),(3,8),
     (2^80,2^80),(2^80,2^81),(1,2^130+1)]
  for (leaders,round) in cases do
    let input:=inputWord leaders round
    let answer:=Executable.candidateAt leaders round
    let output:=outputWord answer
    match TestSparse.finishWithin program 100000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Candidate scheduler exhausted fuel at {leaders},{round}")
    | some (steps,finish)=>
      unless (List.finRange (program.extraRegisters+2)).all (fun r=>
          finish.store r==(if r.val==1 then output else [])) do
        throw (IO.userError s!"Candidate scheduler output/cleanup mismatch at {leaders},{round}")
      unless steps≤4000*(input.length+1) do
        throw (IO.userError "Candidate scheduler exceeded its proved bound")
      IO.println s!"Candidate schedule leaders={leaders}, round={round}: {steps} instructions; all registers clean."
  IO.println "Nineteen complete binary candidate-schedule regressions passed."

#eval tests
end Counting.StackMachine.ProtocolSchedule.Tests
