import Counting.NetworkVistaRunComplete
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.Run.ExecutionTests

def tests : IO Unit := do
  let cases : List (String×Simulation.Input) :=
    [("zero rounds",⟨#[true],#[]⟩),
     ("singleton without arcs",⟨#[true],#[#[#[0]]]⟩),
     ("singleton with parallel loops",⟨#[true],#[#[#[2^12]]]⟩),
     ("two-agent directed cycle",⟨#[true,false],#[#[#[0,1],#[1,0]]]⟩)]
  let program := complete.program
  for (name,input) in cases do
    unless Encoding.networkValid input do
      throw (IO.userError s!"Invalid test network: {name}")
    IO.println s!"Network reconstruction: starting {name}"
    let initial := Routine.inputStore 128 (Encoding.networkInput.encode input)
    let expected := Routine.outputStore 128
      ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input))
    match TestLazy.finishWithin program 50000000 0 (TestLazy.empty program) ⟨0,initial⟩ with
    | none => throw (IO.userError s!"Network reconstruction exceeded fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 130).all (fun r => last.store r == expected r) do
        throw (IO.userError s!"Network reconstruction full-store mismatch: {name}")
      IO.println s!"Network reconstruction: {name} passed ({steps} instructions)."

#eval tests
end Counting.StackMachine.NetworkVista.Run.ExecutionTests
