import Counting.NetworkVistaRunInitial
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.Run.Tests

def tests : IO Unit := do
  let cases : List Simulation.Input :=
    [⟨#[],#[]⟩, ⟨#[true],#[]⟩, ⟨#[false],#[#[#[0]]]⟩,
     ⟨#[true,false,true],#[#[#[0,1,2],#[3,4,5],#[6,7,8]],#[#[]]]⟩,
     ⟨#[true,false],#[#[#[2^130,2^129],#[0,2^128]],#[]]⟩,
     ⟨#[],#[#[],#[#[2^130]] ,#[]]⟩]
  let program := setup.program
  let mut maximum := 0
  for input in cases do
    let initial := Routine.inputStore 128 (Encoding.networkInput.encode input)
    let expected := RealizabilityCall.file (setupData input)
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,initial⟩ with
    | none => throw (IO.userError "Network initialization exceeded fuel")
    | some (steps,last) =>
      unless (List.finRange 130).all (fun r => last.store r == expected r) do
        throw (IO.userError "Network initialization full-store mismatch")
      maximum := max maximum steps
  IO.println s!"Network initialization: {cases.length} full-store cases passed; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.Run.Tests
