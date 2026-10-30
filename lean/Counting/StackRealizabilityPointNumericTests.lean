import Counting.StackRealizabilityPointNumeric
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.PointNumericTests
open Routine

def tests : IO Unit := do
  let cases : List (Nat×Nat×Nat×Nat×Nat×Nat) :=
    [(1,1,3,2,4,4),(1,2,3,2,0,3),(2,2,1,3,0,3),(0,0,0,0,1,0)]
  let mut largest := 0
  let mut count := 0
  for (child,weight,supply,demand,visible,order) in cases do
    for active in [false,true] do
      for accepted in [false,true] do
        let store : Store 58 := fun r =>
          if r=21 then child.bits else if r=43 then weight.bits else if r=37 then supply.bits
          else if r=26 then demand.bits else if r=45 then visible.bits else if r=44 then order.bits
          else if r=1 then [accepted,true,false] else if r=50 then [active,false]
          else if r=0 ∨ r=2 ∨ r=3 then [] else [true,false,true]
        let pass := decide (child≤weight ∧ (order≤visible → supply=demand) ∧
          (visible<order → weight≤child → demand ≤ supply))
        let expected := Function.update (Function.update (Function.update store
          46 (decide (0<weight-child)::store 46)) 47 (decide (demand<supply)::store 47))
          1 [accepted && (!active || pass),true,false]
        let program := pointNumeric.program
        match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
        | none => throw (IO.userError "Point numeric guards exhausted test fuel")
        | some (time,result) =>
          unless (List.finRange 60).all (fun r => result.store r == expected r) do
            throw (IO.userError "Point numeric guards violated full-store contract")
          unless time≤200*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1) do
            throw (IO.userError "Point numeric guards exceeded proved linear bound")
          largest := max largest time
          count := count+1
  IO.println s!"Point numeric guards passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.PointNumericTests
