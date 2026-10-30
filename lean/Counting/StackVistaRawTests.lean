import Counting.StackVistaRawComplete
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.DagUpdate.Raw.Tests
open Routine

def tests : IO Unit := do
  let program := complete.program
  let leader := Executable.initialVista true
  let follower := Executable.initialVista false
  let cases : List (String×Nat×Bool×Nat×Executable.Vista×List (Executable.Vista×Nat)) :=
    [("single isolated leader",0,true,0,leader,[]),
     ("leader self loop",0,true,1,leader,[(leader,1)]),
     ("leader receives follower",0,true,1,leader,[(follower,1)]),
     ("follower receives leader",0,false,1,follower,[(leader,1)]),
     ("parallel loops",0,true,2^40+7,leader,[(leader,2^40+7)]),
     ("zero multiplicity",0,true,0,leader,[(leader,0)]),
     ("malformed old vista",0,false,0,⟨#[],7⟩,[]),
     ("large metadata",2^40,true,2^32,leader,[])]
  for (name,round,flag,degree,old,messages) in cases do
    let input := inputWord round flag degree old messages
    let result := updated round flag degree old messages
    let output := Encoding.vista.encode result
    if old.valid && (old.node old.bottom).level==round && (old.node old.bottom).leader==flag &&
        messages.all (fun message=>message.1.valid && (message.1.node message.1.bottom).level==round) then
      unless result==Executable.rawUpdate old messages degree do
        throw (IO.userError s!"Raw update fixture semantic mismatch: {name}")
    match TestSparse.finishWithin program 30000000 0 (TestSparse.empty program) (initial program input) with
    | none => throw (IO.userError s!"Raw receiver exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange (program.extraRegisters+2)).all
          (fun r=>last.store r==(if r.val==1 then output else [])) do
        throw (IO.userError s!"Raw receiver output or cleanup mismatch: {name}")
      unless steps≤completeBudget round flag degree old messages do
        throw (IO.userError s!"Raw receiver exceeded proved bound: {name}")
      IO.println s!"Raw receiver {name}: {steps} instructions; all 96 registers checked."
  IO.println "Eight raw receiver regressions passed."

#eval tests
end Counting.StackMachine.DagUpdate.Raw.Tests
