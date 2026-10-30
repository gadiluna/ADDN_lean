import Counting.StackRealizabilityPointItem
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.PointItemTests
open Routine

def tests : IO Unit := do
  let nodes : List Executable.Node := [⟨0,none,true,0,[]⟩,
    ⟨1,some 0,true,3,[(0,2)]⟩,⟨1,some 0,false,1,[(0,1)]⟩]
  let cases : List (List Nat × Nat × Nat × Bool × Bool) :=
    [([2,1,1],0,2,true,true),([1,1,1],0,2,true,true),
      ([1,1,1],0,2,false,true),([2,1,1],3,3,true,false)]
  let mut largest := 0
  let mut count := 0
  for (values,old,order,active,accepted) in cases do
    let source := (Encoding.list Encoding.node).encode nodes
    let weights := (Encoding.list Encoding.natural).encode values
    let pairs := nodes.zip values
    let child : Nat := (pairs.map (fun (node,amount) => if node.level=1 ∧ node.parent=some old then amount else 0)).sum
    let supply : Nat := (pairs.map (fun (node,amount) => if node.level=1 ∧ node.parent=some old then amount*node.degree else 0)).sum
    let demand : Nat := (pairs.map (fun (node,amount) => if node.level=1 then amount*Executable.countFrom node old else 0)).sum
    let weight : Nat := values[old]?.getD 0
    let visible : Nat := 2
    let masks := (List.replicate old false)++[active]
    let data : Fin 18→List Bool := fun r => if r=0 then List.replicate old true
      else if r=1 ∨ r=8 then [] else if r=2 then order.bits else if r=3 then visible.bits
      else if r=10 then masks else [true,false]
    let pass := decide (child ≤ weight ∧ (order ≤ visible → supply=demand) ∧
      (visible<order → weight ≤ child → demand ≤ supply))
    let finalData := Function.update (Function.update data 0 (true::data 0)) 4
      (decide (0<weight-child)::data 4)
    let finalData := Function.update finalData 5 (decide (demand<supply)::data 5)
    let store := pointFile (massFile source weights (1:Nat).bits [] old.bits [accepted,true] [] [] []) data
    let expected := pointFile (massFile source weights (1:Nat).bits [] (old+1).bits
      [accepted && (!active || pass),true] [] [] []) finalData
    let program := pointItem.program
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Point item exhausted test fuel")
    | some (time,result) =>
      unless (List.finRange 60).all (fun r => result.store r == expected r) do
        throw (IO.userError "Point item violated preserved full-store contract")
      unless time ≤ 200000100*(pointBodySize nodes values 1 old order visible data)^15 do
        throw (IO.userError "Point item exceeded proved polynomial")
      largest := max largest time
      count := count+1
  IO.println s!"Point item passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.PointItemTests
