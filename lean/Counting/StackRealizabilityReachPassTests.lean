import Counting.StackRealizabilityReachSource
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ReachPassTests
open Routine

private def testPass (size : Nat) (arcs seen : List Bool) : IO Nat:=do
  let store : Store 15:=fun r=>if r=0 then arcs else if r=1 then seen
    else if r=2 then List.replicate size true else if r=8 then [true,false] else []
  let program:=reachPassRoutine.program
  match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Synchronous reachability pass exceeded test fuel")
  | some (time,result)=>
    let expected:=Function.update store 3 (RealizabilityVerifier.BitGraph.reachPass size arcs seen)
    unless (List.finRange 17).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Synchronous reachability pass violated its full-store contract")
    unless time≤10000*(arcs.length+seen.length+size+1)^4 do
      throw (IO.userError "Synchronous reachability pass exceeded its proved bound")
    pure time

private def testSource (size source : Nat) (arcs : List Bool) : IO Nat:=do
  let store : Store 16:=fun r=>if r=0 then arcs else if r=2 then List.replicate size true
    else if r=17 then List.replicate source true else []
  let program:=reachSourceRoutine.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Bounded reachability search exceeded test fuel")
  | some (time,result)=>
    let expected:=Function.update store 1 (reachSourceBits store)
    unless (List.finRange 18).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Bounded reachability search violated its full-store contract")
    if inside : source<size then
      unless result.store 1==RealizabilityVerifier.BitGraph.iterate size arcs ⟨source,inside⟩ size do
        throw (IO.userError "Bounded reachability search disagrees with mathematical iterate")
    unless time≤200000*(arcs.length+size+source+1)^5 do
      throw (IO.userError "Bounded reachability search exceeded its proved bound")
    pure time

def tests : IO Unit:=do
  let mut largest:=0
  for (size,arcs,seen) in [(0,[],[]),(1,[],[]),(1,[false],[true]),
      (2,[false,true,false,false],[true,false]),(2,[false,true,false,false],[false,true]),
      (3,[false,true,false,false,false,true,true,false,false],[true,false,false]),
      (4,[true,false,true],[true])] do
    largest:=max largest (←testPass size arcs seen)
  for (size,source,arcs) in [(0,0,[]),(1,0,[]),(1,0,[true]),(1,2,[true]),
      (2,0,[false,true,false,false]),(2,1,[false,true,false,false]),
      (3,0,[false,true,false,false,false,true,true,false,false]),
      (3,2,[false,true,false,false,false,true,true,false,false]),(4,1,[true,false,true])] do
    largest:=max largest (←testSource size source arcs)
  IO.println s!"Reachability pass/source tests passed 16 cases with full-store checks; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ReachPassTests
