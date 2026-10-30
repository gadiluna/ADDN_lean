import Counting.MachineProtocolInitialize
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.ProtocolInitialize.Tests
open Routine

def run : IO Unit := do
  for (leaders,leader) in [(0,false),(1,true),(2,false),(2^130+5,true)] do
    let input := inputWord leaders leader
    let expected := outputStore 1 (ProtocolAdvance.stateWord (Executable.initialState leaders leader))
    match TestLazy.finishWithin complete.program 100000 0 (TestLazy.empty complete.program)
      ⟨0,inputStore 1 input⟩ with
    | none => throw (IO.userError "Initialization exhausted fuel")
    | some (steps,last) =>
      unless (List.finRange 3).all (fun r=>last.store r==expected r) do
        throw (IO.userError "Initialization full-store mismatch")
      unless steps ≤ 100*(input.length+1) do
        throw (IO.userError "Initialization exceeded proved runtime")
      IO.println s!"Initialization {leaders}/{leader}: {steps} steps; all registers checked."
  IO.println "Four initialization regressions passed."

#eval run
end Counting.StackMachine.ProtocolInitialize.Tests

