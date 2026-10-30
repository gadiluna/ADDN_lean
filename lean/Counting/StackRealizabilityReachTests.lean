import Counting.StackRealizabilityReachSpec
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ReachTests
open Routine

private def testTarget (size : Nat) (arcs seen : List Bool) (target : Fin size) : IO Unit:=do
  let width:=List.replicate size true
  let store : Store 12:=fun r=>if r=0 then arcs else if r=1 then seen else if r=2 then width
    else if r=4 then List.replicate target.val true else if r=5 then
      RealizabilityVerifier.BitGraph.bitAt seen target.val::[false,true]
    else if r=8 then [true,false] else if r=13 then width else []
  let program:=(forEach 13 reachItem).program
  match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Reachability target scan exceeded test fuel")
  | some (time,result)=>
    let expected:=reachLoopStore store (RealizabilityVerifier.BitGraph.bitAt seen target.val) [false,true] width
    unless (List.finRange 14).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Reachability target scan violated its full-store contract")
    unless result.store 5==RealizabilityVerifier.BitGraph.bitAt
        (RealizabilityVerifier.BitGraph.reachPass size arcs seen) target.val::[false,true] do
      throw (IO.userError "Reachability target scan disagrees with reachPass")
    unless time≤width.length*(60*(arcs.length+seen.length+width.length+target.val+1+
        width.length*(width.length+1))+2)+1 do
      throw (IO.userError "Reachability target scan exceeded its proved bound")

def tests : IO Unit:=do
  for (size,arcs,seen) in [
      (1,[],[]),(1,[true],[false]),(1,[false],[true]),
      (2,[false,true,false,false],[true,false]),
      (2,[false,true,false,false],[false,true]),
      (3,[false,true,false,false,false,true,true,false,false],[true,false,false]),
      (3,[false,true,false,false,false,true,true,false,false],[false,true,false]),
      (4,[true,false,true],[true])] do
    for target in List.finRange size do testTarget size arcs seen target
  IO.println "Reachability predecessor loop passed 17 target scans against reachPass, including truncated bit vectors and asymmetric arcs."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ReachTests
