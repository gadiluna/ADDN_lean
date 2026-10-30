import Counting.StackRealizabilityArcPoint
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ArcPointTests
open Routine RealizabilityVerifier.CompactGraph

def tests : IO Unit:=do
  let mut cases:=0
  let mut largest:=0
  let sources : List (List Bool):=[[false,true,false],[true,false,false],[false,false,true],
    [false,true,false],[true,false,false],[false,false,false],
    [false,false,false,true,false,false,false,false,false],
    [false,false,false,true,false,false,false,false,false]]
  for x in [0,1,2,4] do
    for y in [0,1,2,4] do
      for tail in [[],[true,false]] do
        let store : Store 30:=fun r=>if r.val<8 then sources[r.val]?.getD []
          else if r=8 then List.replicate x true else if r=9 then List.replicate y false
          else if r=10 then List.replicate (x*3+y) true else if r=11 then List.replicate (y*3+x) false
          else if r=24 then tail else if r=25 then [true,false,true] else []
        let program:=arcPoint.program
        match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
        | none=>throw (IO.userError "Arc point exceeded fuel")
        | some (time,result)=>
          let expected:=Function.update store 24 (arcPointValue store::tail)
          unless (List.finRange 32).all (fun r=>result.store r==expected r) do
            throw (IO.userError "Arc point violated full-store contract")
          unless time≤1000*arcReadSize store do throw (IO.userError "Arc point exceeded proved linear bound")
          largest:=max largest time
          cases:=cases+1
  IO.println s!"Realizability arc point passed {cases} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ArcPointTests
