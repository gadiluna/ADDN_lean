import Counting.StackRealizabilityOutsideVector
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.OutsideVectorTests
open Routine

def tests : IO Unit := do
  let mut count := 0
  let mut largest := 0
  for (order,visible) in ([(0,0),(1,0),(1,1),(2,4),(2^100,2^99),(2^100,2^100)]:List (Nat×Nat)) do
    for width in [0,1,4] do
      let store : Store 7 := ![order.bits,visible.bits,List.replicate width true,[true,false],[],[false,true],[],[],[]]
      let expected := Function.update store 3 (List.replicate (width-1) false++decide (visible<order)::[true,false])
      let program := outsideVector.program
      match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none => throw (IO.userError "Outside vector exhausted test fuel")
      | some (time,result) =>
        unless (List.finRange 9).all (fun r => result.store r == expected r) do
          throw (IO.userError "Outside vector violated complete-store contract")
        unless time ≤ 40*(order.size+visible.size+width+1) do
          throw (IO.userError "Outside vector exceeded proved linear bound")
        largest := max largest time
        count := count+1
  IO.println s!"Outside vector passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.OutsideVectorTests
