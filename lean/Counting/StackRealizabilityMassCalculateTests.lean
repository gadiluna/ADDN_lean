import Counting.StackRealizabilityMassCalculate
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.MassCalculateTests
open Routine

def tests : IO Unit := do
  let basic : List Executable.Node := [⟨0,none,true,1,[]⟩,⟨1,some 0,false,2,[(0,3)]⟩]
  let triple : List Executable.Node := [⟨0,none,true,1,[]⟩,
    ⟨1,some 0,false,3,[(0,2)]⟩,⟨1,some 0,true,1,[(0,1),(1,4)]⟩]
  let large : List Executable.Node := [⟨0,none,true,0,[]⟩,
    ⟨1,some 0,false,2^24,[(0,2^20)]⟩]
  let cases : List (List Executable.Node × List Nat × Nat × Nat × Bool) :=
    [([],[],1,0,true),(basic,[1,2],1,0,true),(basic,[1,2],1,1,true),
      (basic,[1,2],2,0,false),(triple,[2,3,5],1,0,true),
      (triple,[2,0,5],1,1,false),(large,[1,2^16],1,0,true),(large,[1,2^16],0,3,true)]
  let mut largest := 0
  let mut count := 0
  for (nodes,values,target,old,accepted) in cases do
    let source := (Encoding.list Encoding.node).encode nodes ++ [true,false]
    let weights := (Encoding.list Encoding.natural).encode values ++ [false,true,true]
    let status := [accepted,false,true]
    let pairs := nodes.zip values
    let child := (pairs.map (fun (node,amount) =>
      if node.level=target ∧ node.parent=some old then amount else 0)).sum
    let supply := (pairs.map (fun (node,amount) =>
      if node.level=target ∧ node.parent=some old then amount*node.degree else 0)).sum
    let demand := (pairs.map (fun (node,amount) =>
      if node.level=target then amount*Executable.countFrom node old else 0)).sum
    let store := massFile source weights target.bits [] old.bits status [] [] []
    let expected := massFile source weights target.bits [] old.bits status child.bits demand.bits supply.bits
    let program := massCalculate.program
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Mass composition exhausted test fuel")
    | some (time,result) =>
      unless (List.finRange 42).all (fun r => result.store r == expected r) do
        throw (IO.userError "Mass composition violated full-store mathematical contract")
      unless time ≤ 100000000*(source.length+weights.length+target.size+old.size+2)^15 do
        throw (IO.userError "Mass composition exceeded proved polynomial")
      largest := max largest time
      count := count+1
  IO.println s!"Mass composition passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.MassCalculateTests
