import Counting.StackRealizabilityWeightLookup
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.WeightLookupTests
open Routine

def roles : Fin 8 ↪ Fin 12 := ⟨![8,2,10,1,4,7,3,11],by decide⟩

def tests : IO Unit := do
  let mut largest := 0
  let mut count := 0
  for values in [[],[0,7,2^100]] do
    for index in [0,1,2,3,8] do
      for output in [[],[true,false]] do
        let source := (Encoding.list Encoding.natural).encode values
        let store : Store 10 := fun r =>
          if r=roles 0 then source else if r=roles 1 then List.replicate index false
          else if r=roles 2 then output else if r=roles 3 then [false,true]
          else if r=roles 4 ∨ r=roles 5 ∨ r=roles 6 ∨ r=roles 7 then [] else [true,false,true]
        let expected := Function.update store (roles 2) ((values[index]?.getD 0).bits++output)
        let program := (weightLookup 4 roles).program
        match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
        | none => throw (IO.userError "Weight lookup exhausted test fuel")
        | some (time,result) =>
          unless (List.finRange 12).all (fun r => result.store r == expected r) do
            throw (IO.userError "Weight lookup violated full-store contract")
          unless time ≤ 10*source.length+8*index+28 do
            throw (IO.userError "Weight lookup exceeded proved linear bound")
          largest := max largest time
          count := count+1
  IO.println s!"Weight lookup passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.WeightLookupTests
