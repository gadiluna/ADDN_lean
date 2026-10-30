import Counting.StackProtocolUpdateComplete
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.ProtocolUpdate.Tests

def tests : IO Unit := do
  let program:=complete.program
  let leader:=Executable.initialVista true
  let follower:=Executable.initialVista false
  let cases : List (String×Executable.Vista×List (Executable.Vista×Nat)×Nat):=
    [("single isolated leader",leader,[],0),
     ("follower receives repeated leader messages",follower,[(leader,3)],2)]
  for (name,old,messages,degree) in cases do
    let input:=inputWord old messages degree
    let expected:=outputWord (Executable.updateVista? old messages degree)
    match TestSparse.finishWithin program 3000000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Complete vista updater exhausted fuel: {name}")
    | some (steps,last)=>
      unless (List.finRange (program.extraRegisters+2)).all (fun r=>
          last.store r==(if r.val==1 then expected else [])) do
        throw (IO.userError s!"Complete vista updater output or cleanup mismatch: {name}")
      IO.println s!"Complete vista updater {name}: {steps} instructions; all 160 registers checked."

#eval tests
end Counting.StackMachine.ProtocolUpdate.Tests
