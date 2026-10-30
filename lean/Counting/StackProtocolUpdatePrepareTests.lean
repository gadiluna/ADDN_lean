import Counting.StackProtocolUpdatePrepare
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.ProtocolUpdate.PrepareTests
open Routine NetworkComplement

def tests : IO Unit := do
  let program:=prepare.program
  let leader:=Executable.initialVista true
  let follower:=Executable.initialVista false
  let cases : List (String×Executable.Vista×List (Executable.Vista×Nat)×Nat):=
    [("empty incoming list",leader,[],0),
     ("two distinct message bundles",follower,[(leader,3),(follower,2)],5),
     ("binary multiplicity",leader,[(leader,2^40+7)],2^40+7)]
  for (name,old,messages,degree) in cases do
    let input:=inputWord old messages degree
    let expected:=file (preparedData old messages degree)
    match TestSparse.finishWithin program 100000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Updater field extraction exhausted fuel: {name}")
    | some (steps,last)=>
      unless (List.finRange 160).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Updater field extraction full-store mismatch: {name}")
      IO.println s!"Updater field extraction {name}: {steps} instructions; all 160 registers checked."

#eval tests
end Counting.StackMachine.ProtocolUpdate.PrepareTests
