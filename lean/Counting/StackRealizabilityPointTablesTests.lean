import Counting.StackRealizabilityPointTables
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.PointTablesTests
open Routine

def tests : IO Unit := do
  let cases : List (List Executable.Node × List Nat × Nat × Nat × Nat × List Bool × Nat) :=
    [([],[],1,1,0,[],0),([],[],1,1,0,[false],1),
      ([⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,1)]⟩],[1,1],1,1,1,[true,false,false],3),
      ([⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,2)]⟩],[1,1],1,1,1,[true,false,false],3)]
  let mut largest := 0
  let mut count := 0
  for (nodes,values,target,order,visible,masks,width) in cases do
    let pairs := nodes.zip values
    let child : Nat→Nat := fun old => (pairs.map (fun (node,amount) => if node.level=target ∧ node.parent=some old then amount else 0)).sum
    let supply : Nat→Nat := fun old => (pairs.map (fun (node,amount) => if node.level=target ∧ node.parent=some old then amount*node.degree else 0)).sum
    let demand : Nat→Nat := fun old => (pairs.map (fun (node,amount) => if node.level=target then amount*Executable.countFrom node old else 0)).sum
    let leaving := (List.range width).map (fun old => decide (0<values[old]?.getD 0-child old))
    let deficit := (List.range width).map (fun old => decide (demand old<supply old))
    let accepted := (List.range width).all (fun old => !masks[old]?.getD false ||
      decide (child old ≤ values[old]?.getD 0 ∧ (order ≤ visible → supply old=demand old) ∧
        (visible<order → values[old]?.getD 0 ≤ child old → demand old ≤ supply old)))
    let data : Fin 18→List Bool := fun r => if r=1 ∨ r=6 ∨ r=7 ∨ r=8 then []
      else if r=2 then order.bits else if r=3 then visible.bits else if r=10 then masks
      else if r=11 then List.replicate width false else [true,false]
    let store := pointLoopStore nodes values target 0 [true,false] data [] [] [] []
    let expected := pointLoopStore nodes values target 0 [accepted,false]
      (Function.update (Function.update data 6 leaving) 7 deficit) [] [] [] []
    let program := pointTables.program
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Point tables exhausted test fuel")
    | some (time,result) =>
      unless (List.finRange 60).all (fun r => result.store r == expected r) do
        throw (IO.userError "Point tables violated full-store ordered-table contract")
      unless time ≤ 300000000*(pointTablesSize nodes values target order visible data)^16 do
        throw (IO.userError "Point tables exceeded proved polynomial")
      largest := max largest time
      count := count+1
  IO.println s!"Point tables passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.PointTablesTests
