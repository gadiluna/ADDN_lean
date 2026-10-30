import Counting.StackRealizabilityNodeIncidence
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.NodeIncidenceTests
open Routine

def tests : IO Unit:=do
  let cases : List (Executable.Node×Nat):=[(⟨0,none,true,0,[]⟩,0),
    (⟨1,some 0,false,2,[(0,2)]⟩,0),(⟨1,some 1,false,2,[(0,2)]⟩,0),
    (⟨1,some 0,true,0,[(0,0),(0,4)]⟩,0),(⟨1,none,false,3,[(0,4),(0,0)]⟩,0),
    (⟨2,some 1,true,2^120,[(0,1),(1,2^128)]⟩,1),
    (⟨2^110,some (2^100),false,2^120,[(2^100,0),(2^100,2^129)]⟩,2^100),
    (⟨2^110,some (2^100),false,2^120,[(0,2^129)]⟩,2^100+1)]
  let mut largest:=0
  for (node,query) in cases do
    for output in [[],[false,true]] do
      let suffix:=[false,true,false]
      let store:=AnchorCoefficient.file (Encoding.node.encode node++suffix) query.bits output [] [] [] [] [] [] []
      let expected:=AnchorCoefficient.file suffix query.bits (decide (0<Executable.countFrom node query)::output)
        [] [] [] [] [] [] [decide (node.parent=some query)]
      let program:=nodeIncidence.program
      match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Node incidence exceeded test fuel")
      | some (time,result)=>
        unless (List.finRange 34).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Node incidence violated full-store contract")
        unless time≤8000*((Encoding.node.encode node).length+suffix.length+query.size+1)^3 do
          throw (IO.userError "Node incidence exceeded proved bound")
        largest:=max largest time
  IO.println s!"Realizability node incidence passed 16 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.NodeIncidenceTests
