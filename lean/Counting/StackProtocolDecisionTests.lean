import Counting.MachineProtocolDecision
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.ProtocolDecision.Tests

def tests : IO Unit := do
  let program:=complete.program
  let mut cases : List (String×Nat×Executable.Vista):=
    [("leader before first round",1,Executable.initialVista true),
      ("follower before first round",2,Executable.initialVista false)]
  match Executable.updateVista? (Executable.initialVista true) [] 0 with
  | some vista=>cases:=cases++[("all-leader early stop",1,vista)]
  | none=>throw (IO.userError "Could not construct depth-one vista")
  for (name,leaders,vista) in cases do
    let input:=inputWord vista leaders
    let expected:=outputWord (Executable.scheduledPlan leaders vista).eval
    match TestSparse.finishWithin program 1000000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Scheduled decision exhausted fuel: {name}")
    | some (steps,finish)=>
      unless (List.finRange (program.extraRegisters+2)).all (fun r=>
          finish.store r==(if r.val==1 then expected else [])) do
        throw (IO.userError s!"Scheduled decision output/cleanup mismatch: {name}")
      IO.println s!"Scheduled decision {name}: {steps} instructions, every register checked."
  IO.println "Three complete scheduled-decision control regressions passed."

#eval tests
end Counting.StackMachine.ProtocolDecision.Tests
