import Counting.StackRealizabilityArcMatrix
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ArcMatrixTests
open Routine

def tests : IO Unit:=do
  let mixed : List (List Bool):=[[false,true,false],[true,false,false],[false,false,true],
    [false,true,false],[true,false,false],[false,false,false],
    [false,false,false,true,false,false,false,false,false],
    [false,false,false,true,false,false,false,false,false]]
  let cases : List (List (List Bool)×Nat):=[([],0),([],1),
    ([[true],[true],[false],[true],[false],[false],[true],[false]],1),
    ([[false,true],[true,false],[],[false,true],[],[],[false,false,true,false],[false,false,true,false]],2),
    ([[false,true],[true,false],[],[false,false],[],[],[false,false,true,false],[false,false,true,false]],2),
    (mixed,3),(mixed,4),([[false],[true],[false,false,true],[],[false],[true]],3)]
  let mut largest:=0
  for (sources,width) in cases do
    for bit in [false,true] do
      let store : Store 30:=fun r=>if r.val<8 then sources[r.val]?.getD []
        else if r=29 then List.replicate width bit else if r=25 then [true,false,true] else []
      let expectedBits:=(List.range width).flatMap (fun x=>(List.range width).map
        (fun y=>arcCell (arcTables store) x y (x*width+y) (y*width+x)))
      let expected:=Function.update store 30 expectedBits
      let program:=arcMatrix.program
      match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Arc matrix exceeded test fuel")
      | some (time,result)=>
        unless (List.finRange 32).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Arc matrix violated full-store row-major contract")
        unless time≤1000000*(arcReadSize store+width)^7 do
          throw (IO.userError "Arc matrix exceeded proved polynomial")
        largest:=max largest time
  IO.println s!"Realizability arc matrix passed 16 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ArcMatrixTests
