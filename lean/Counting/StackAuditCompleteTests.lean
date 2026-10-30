import Counting.StackAuditComplete
import Counting.StackAuditCompleteEncoding
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.AuditComplete.Tests

def tests : IO Unit := do
  let program:=complete.program
  let root:=Executable.initialVista true
  let next : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let chain : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,
    ⟨2,some 1,true,0,[]⟩],2⟩
  let cases : List (String×Executable.Vista×Nat×Nat×Nat×Option Executable.AuditWitness):=
    [("malformed empty vista",⟨#[],0⟩,1,1,1,none),
     ("insufficient depth",root,1,1,1,none),
     ("zero leaders",next,0,1,1,none),
     ("zero last",next,1,1,0,none),
     ("binary oversize last",next,1,1,2^80,none),
     ("complete success",next,1,1,1,some ⟨1,#[1,1]⟩),
     ("post-solver sum rejection",next,1,2,1,none),
     ("latest anchor success",chain,1,1,2,some ⟨2,#[1,1,1]⟩)]
  for (name,vista,leaders,candidate,last,answer) in cases do
    unless Executable.audit? vista leaders candidate last==answer do
      throw (IO.userError s!"Whole-audit fixture has unexpected specification: {name}")
    let input:=AuditPrefix.inputWord vista leaders candidate last
    let output:=witnessWord answer
    unless answerCodec.decodeExact output==some answer do
      throw (IO.userError s!"Whole-audit output codec mismatch: {name}")
    match TestSparse.finishWithin program 20000000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Whole-audit regression exhausted fuel: {name}")
    | some (steps,finish)=>
      unless (List.finRange (program.extraRegisters+2)).all (fun r=>
          finish.store r==(if r.val==1 then output else [])) do
        throw (IO.userError s!"Whole-audit answer or register cleanup mismatch: {name}")
      IO.println s!"Whole audit {name}: {steps} instructions; full output witness and all registers checked."
  IO.println "Eight whole-audit regressions passed."

#eval tests
end Counting.StackMachine.AuditComplete.Tests
