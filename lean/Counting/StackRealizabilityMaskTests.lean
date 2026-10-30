import Counting.StackRealizabilityMaskTable
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.MaskTests
open Routine

private def test (nodes : List Executable.Node) (old next : Nat) (accepted : Bool) : IO Nat:=do
  let store : Store 28:=fun r=>if r=17 then Encoding.sequence Encoding.node nodes++[false,true,false]
    else if r=1 then accepted::[true,false] else if r=20 then List.replicate nodes.length false
    else if r=22 then old.bits else if r=23 then next.bits else []
  let program:=maskTable.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Realizability mask table exceeded test fuel")
  | some (time,result)=>
    unless (List.finRange 30).all (fun r=>result.store r==maskTableStore store nodes old next r) do
      throw (IO.userError "Realizability mask table violated its full-store contract")
    unless time≤9000*((store 17).length+old.size+next.size+1)^5 do
      throw (IO.userError "Realizability mask table exceeded its proved bound")
    pure time

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let first:Executable.Node:=⟨1,some 0,true,2,[(0,4)]⟩
  let second:Executable.Node:=⟨2,some 1,false,2^128,[(0,0),(0,5)]⟩
  let huge:Executable.Node:=⟨2^100,some (2^80),false,0,[(2^60,2^129)]⟩
  let mut largest:=0
  for (nodes,old,next) in [([],0,1),([root],0,1),([root,first,second],0,1),
      ([root,first,second],1,2),([huge,root,second],2^100,2),([root,first],7,7)] do
    for accepted in [false,true] do largest:=max largest (←test nodes old next accepted)
  IO.println s!"Realizability old/new/degree masks passed 12 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.MaskTests
