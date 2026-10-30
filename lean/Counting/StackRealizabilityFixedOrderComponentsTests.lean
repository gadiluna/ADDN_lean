import Counting.StackRealizabilityFixedOrderEntry
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.FixedOrderRecognition.ComponentTests
open Routine RealizabilityCall

private def requireRun (label : String) (routine : Routine 128) (start expected : Store 128) : IO Nat := do
  let program := routine.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,start⟩ with
  | none => throw (IO.userError s!"Fixed-order component exhausted fuel: {label}")
  | some (time,result) =>
    unless (List.finRange 130).all (fun r=>result.store r==expected r) do
      throw (IO.userError s!"Fixed-order component violated full-store contract: {label}")
    return time

def tests : IO Unit := do
  let root : Executable.Node := ⟨0,none,true,0,[]⟩
  let vista : Executable.Vista := ⟨#[root],0⟩
  let mut maximum := 0
  let mut count := 0
  for (ell,order,counts) in [(1,1,[1]),(2^100,2^120,[2^110,1])] do
    let input := Encoding.fixedOrderInput.encode (vista,ell,order)
    let witness := (Encoding.list Encoding.natural).encode counts
    let data := VistaComplement.initialData input witness true
    let t ← requireRun "input and certificate assembly" allFields (file data)
      (file (allFieldsData data vista ell order))
    maximum := max maximum t
    count := count+1
  let input := Encoding.fixedOrderInput.encode (vista,1,1)
  let witness := (Encoding.list Encoding.natural).encode [1]
  for (rawInput,rawWitness) in [(input,witness),([],witness),(input,[]),(input,witness++[true])] do
    let data := VistaComplement.initialData rawInput rawWitness true
    let t ← requireRun "canonical syntax and malformed rejection" syntaxChecks (file data)
      (file (Function.update data 4 [syntaxAccepted rawInput rawWitness]))
    maximum := max maximum t
    count := count+1
  IO.println s!"Fixed-order components passed {count} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.FixedOrderRecognition.ComponentTests
