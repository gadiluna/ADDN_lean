import Counting.StackCompareLengthEquality

namespace Counting.StackMachine.Compare.LengthEqualityTests
open Routine

def roles : Fin 6 ↪ Fin 8 := ⟨![4,0,6,2,5,7],by decide⟩

def tests : IO Unit := do
  let lefts : List (List Bool) := [[],[true],[false],[true,false],[false,true,false],List.replicate 64 false,List.replicate 128 true]
  for left in lefts do
    for count in [0,1,2,3,5,64,128] do
      for suffix in [[],[false,true]] do
        let right := List.replicate count true
        let store : Fin 8 → List Bool := ![right,[true,false],[],[false,true],left,[],suffix,[]]
        let expected := Function.update store 6 (decide (left.length=count)::suffix)
        let routine := preservingLengthEquality 2 roles
        let cost := preservingLengthEqualityCost left right
        match Machine.run (step routine.program) cost ⟨0,store⟩ with
        | none => throw (IO.userError "Unary length equality halted before exact cost")
        | some finish =>
          unless (step routine.program finish).isNone &&
              (List.finRange 8).all (fun r => finish.store r==expected r) && cost≤6*(left.length+right.length)+11 do
            throw (IO.userError "Unary length equality whole-store or cost mismatch")
  IO.println "Unary length equality passed 98 full-store executions with permuted roles."

#eval tests
end Counting.StackMachine.Compare.LengthEqualityTests
