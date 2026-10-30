import Counting.StackRealizabilityMaskPrefix
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.MaskPrefixTests
open Routine

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let next:Executable.Node:=⟨1,some 0,true,2^128,[(0,2^90)]⟩
  let mut largest:=0
  for (nodes,round) in [([],0),([root],0),([root,next],0),([root,next],2^100)] do
    for accepted in [false,true] do
      let suffix:=[false,true,false]
      let store : Store 28:=fun r=>if r=17 then (Encoding.list Encoding.node).encode nodes++suffix
        else if r=1 then accepted::[true,false] else if r=22 then round.bits else if r=23 then (round+1).bits else []
      let program:=maskPrefix.program
      match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Realizability mask prefix exceeded test fuel")
      | some (time,result)=>
        let expected:=maskPrefixStore store nodes suffix round (round+1)
        unless (List.finRange 30).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Realizability mask prefix violated its full-store contract")
        unless time≤11000*((store 17).length+round.size+(round+1).size+1)^5 do
          throw (IO.userError "Realizability mask prefix exceeded its proved polynomial")
        largest:=max largest time
  IO.println s!"Realizability mask header/prefix passed 8 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.MaskPrefixTests
