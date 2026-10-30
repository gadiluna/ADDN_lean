import Counting.MachineProtocolVista
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.ProtocolVista.Tests

def tests : IO Unit := do
  let program:=complete.program
  let mut cases : List (String×Executable.Vista):=
    [("leader root",Executable.initialVista true),("follower root",Executable.initialVista false)]
  match Executable.updateVista? (Executable.initialVista true) [] 0 with
  | some vista=>cases:=cases++[("zero-message level one",vista)]
  | none=>throw (IO.userError "Could not construct valid depth-one vista")
  match Executable.updateVista? (Executable.initialVista true) [(Executable.initialVista false,1)] 0 with
  | some vista=>cases:=cases++[("mixed leader roots",vista)]
  | none=>throw (IO.userError "Could not construct valid mixed-root vista")
  for (name,vista) in cases do
    unless vista.valid do throw (IO.userError s!"Invalid fixture: {name}")
    let input:=Encoding.vista.encode vista
    let expected:=outputWord vista
    match TestSparse.finishWithin program 1000000 0 (TestSparse.empty program) (initial program input) with
    | none=>throw (IO.userError s!"Vista summary fuel exhausted: {name}")
    | some (steps,finish)=>
      unless (List.finRange (program.extraRegisters+2)).all (fun r=>
          finish.store r==(if r.val==1 then expected else [])) do
        throw (IO.userError s!"Vista summary output/cleanup mismatch: {name}")
      unless steps≤ 3000000*(input.length+1)^5 do
        throw (IO.userError "Vista summary exceeded its proved bound")
      IO.println s!"Vista summary {name}: {steps} instructions, every register checked."
  IO.println "Four complete vista-summary regressions passed."

#eval tests
end Counting.StackMachine.ProtocolVista.Tests
