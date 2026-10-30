import Counting.StackRealizabilityIncoming
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.IncomingTests
open Routine

def tests : IO Unit:=do
  let mut largest:=0
  for (edges,query) in [([],0),([(0,0)],0),([(0,3)],0),([(0,3)],1),
      ([(0,0),(0,8)],0),([(0,8),(0,0)],0),([(1,3),(0,0),(2,5)],2),
      ([(2^100,2^129)],2^100),([(2^100,2^129)],0)] do
    let node:Executable.Node:=⟨1,some 0,false,0,edges⟩
    let suffix:=[true,false,true]
    let store:=AnchorFind.bank
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix)
      query.bits [] [] [] []
    let program:=incomingPositive.program
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Incoming-positive scan exceeded test fuel")
    | some (time,result)=>
      let expected:=AnchorFind.bank suffix query.bits [] [decide (0<Executable.countFrom node query)] [] []
      unless (List.finRange 21).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Incoming-positive scan violated its first-match/full-store contract")
      unless time≤6000*((Encoding.node.encode node).length+suffix.length+query.size+1)^3 do
        throw (IO.userError "Incoming-positive scan exceeded its proved polynomial")
      largest:=max largest time
  IO.println s!"Incoming-positive scan passed 9 first-match/full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.IncomingTests
