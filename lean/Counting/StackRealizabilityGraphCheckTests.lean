import Counting.StackRealizabilityGraphCheckSpec
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.GraphCheckTests
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
  for (sources,size) in cases do
    for accepted in [false,true] do
      IO.println s!"Checking graph fields: width={size}, accepted={accepted}"
      let tables : Fin 8→List Bool:=fun i=>sources[i.val]?.getD []
      let width:=List.replicate size false
      let tail:=[true,false]
      let store:=graphFile tables width (accepted::tail) [] []
      let arcs:=(List.range size).flatMap (fun x=>(List.range size).map
        (fun y=>arcCell tables x y (x*size+y) (y*size+x)))
      let active:=(List.range size).map (activeBit (tables 0) (tables 1) (tables 2))
      let expected:=graphFile tables width ((accepted && RealizabilityVerifier.BitGraph.check size arcs active)::tail) [] []
      let program:=graphCheckRoutine.program
      match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Graph field checker exceeded test fuel")
      | some (time,result)=>
        unless (List.finRange 42).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Graph field checker violated full-store contract")
        unless time≤30000000000*(graphSize tables width)^12 do
          throw (IO.userError "Graph field checker exceeded proved polynomial")
        largest:=max largest time
  IO.println s!"Realizability graph construction/connectivity passed 16 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.GraphCheckTests
