import Counting.StackRealizabilityReachCheck
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ReachCheckTests
open Routine

private def test (size : Nat) (arcs active : List Bool) (accepted : Bool) : IO Nat:=do
  let store : Store 22:=fun r=>if r=0 then arcs else if r=2 then List.replicate size false
    else if r=18 then active else if r=19 then accepted::[false,true] else []
  let program:=reachCheckRoutine.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Active strong-connectivity checker exceeded test fuel")
  | some (time,result)=>
    let expected:=Function.update store 19 ((accepted && RealizabilityVerifier.BitGraph.check size arcs active)::[false,true])
    unless (List.finRange 24).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Active strong-connectivity checker violated its full-store or Boolean contract")
    unless time≤7000000*(arcs.length+active.length+size+1)^6 do
      throw (IO.userError "Active strong-connectivity checker exceeded its proved bound")
    pure time

def tests : IO Unit:=do
  let mut largest:=0
  for (size,arcs,active) in [(0,[],[]),(1,[],[true]),(1,[true],[true]),
      (2,[],[]),(2,[],[true,false]),(2,[],[true,true]),
      (2,[false,true,false,false],[true,true]),(2,[false,true,true,false],[true,true]),
      (3,[false,true,false,false,false,true,true,false,false],[true,true,true]),
      (3,[false,true,false,false,false,true,false,false,false],[true,false,true]),
      (3,[false,true,false,false,false,true,true,false,false],[true]),
      (4,[true,false,true],[true,true,false,true])] do
    for accepted in [false,true] do largest:=max largest (←test size arcs active accepted)
  IO.println s!"Active strong-connectivity checker passed 24 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ReachCheckTests
