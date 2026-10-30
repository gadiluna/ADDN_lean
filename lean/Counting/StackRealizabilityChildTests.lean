import Counting.StackRealizabilityChildPrefix
import Counting.StackRealizabilityWeightedAccumulate
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.ChildTests
open Routine

private def requireChildren (nodes : List Executable.Node) (values : List Nat)
    (round old total : Nat) (accepted : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Child scan test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 25:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=21 then total.bits else if r=22 then (round+1).bits else if r=25 then (old+1).bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let count:=RealizabilityVerifier.childCount vista values.toArray round old
  match DagValidation.TestRun.run childPrefix.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Child count scan exceeded test fuel")
  | some (steps,result)=>
    let final:=childPrefixStore store nodes values (round+1) old total nodeSuffix weightSuffix
    unless (List.finRange 27).all (fun r=>result.store r==final r) do
      throw (IO.userError "Child count scan violated its full-store contract")
    unless result.store 21==(total+count).bits && result.store 1==(accepted::[false,true]) do
      throw (IO.userError "Child count scan disagrees with actual verifier childCount")
    unless steps≤13000*((store 17).length+(store 20).length+total.size+(round+1).size+(old+1).size+1)^5 do
      throw (IO.userError "Child count scan exceeded proved polynomial")
    IO.println s!"Child count: {nodes.length} stored nodes, {steps} stack instructions; exact count {count}."

private def requireProduct (first second total : Nat) : IO Unit:=do
  let store : Store 12:=fun r=>if r=0 then first.bits else if r=1 then second.bits else if r=13 then total.bits else []
  match DagValidation.TestRun.run weightedAccumulate.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Weighted accumulation exceeded test fuel")
  | some (steps,result)=>
    let final:=Function.update store 13 (total+first*second).bits
    unless (List.finRange 14).all (fun r=>result.store r==final r) do
      throw (IO.userError "Weighted accumulation violated its full-store contract")
    unless steps≤83000*(first.size+second.size+total.size+1)^3 do
      throw (IO.userError "Weighted accumulation exceeded proved polynomial")
    IO.println s!"Weighted accumulation: {steps} stack instructions."

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let a:Executable.Node:=⟨1,some 0,true,1,[(0,3)]⟩
  let b:Executable.Node:=⟨1,some 1,false,2,[(0,1)]⟩
  let c:Executable.Node:=⟨2,some 0,true,1,[]⟩
  requireChildren [] [] 0 0 8 true
  requireChildren [root] [8] 0 0 0 true
  requireChildren [root,a] [8,5] 0 0 0 true
  requireChildren [root,a,a,b,c] [8,2,3,7,11] 0 0 4 true
  requireChildren [root,a,a,b,c] [8,2,3,7,11] 0 1 4 true
  requireChildren [root,a,a,b,c] [8,2,3,7,11] 1 0 4 true
  requireChildren [root,a,b] [8,0,2] 0 0 0 false
  requireChildren [a,b] [2^128,2^128+1] 0 0 (2^128) true
  requireChildren [a,b] [2,3] 0 (2^128) 7 true
  requireChildren [{a with level:=2^128}] [2^128] (2^128-1) 0 0 true
  requireProduct 0 0 5
  requireProduct 0 (2^128) 7
  requireProduct 3 5 7
  requireProduct 2 (2^128+1) (2^128)
  requireProduct (2^64+1) (2^64-1) 1
  IO.println "Child counting passed 10 full-store cases; weighted accumulation passed 5 preserved-operand cases."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ChildTests
