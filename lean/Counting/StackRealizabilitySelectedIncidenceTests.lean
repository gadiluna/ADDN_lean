import Counting.StackRealizabilitySelectedIncidence
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.SelectedIncidenceTests
open Routine

def tests : IO Unit := do
  let nodes : List Executable.Node := [⟨0,none,true,0,[]⟩,
    ⟨1,some 0,false,3,[(0,0),(0,9),(1,4)]⟩,
    ⟨2,some 1,true,2^110,[(0,2^120),(1,3)]⟩]
  let source := Encoding.sequence Encoding.node nodes ++ [false,true,true]
  let mut largest := 0
  let mut count := 0
  for position in List.finRange nodes.length do
    for query in [0,1,5,2^100] do
      for accepted in [false,true] do
        let index := List.replicate position.val false
        let incoming := [true,false]
        let parent := [false,true,false]
        let status := [accepted,false,true]
        let store := incidenceFile source index query.bits incoming parent status
        let node := nodes[position]
        let expected := incidenceFile source index query.bits
          (decide (0 < Executable.countFrom node query)::incoming)
          (decide (node.parent = some query)::parent) status
        let program := selectedIncidence.program
        match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
        | none => throw (IO.userError "Selected incidence exhausted test fuel")
        | some (time,result) =>
          unless (List.finRange 42).all (fun r => result.store r == expected r) do
            throw (IO.userError "Selected incidence violated whole-store contract")
          unless time ≤ 20000*(source.length+query.size+1)^4 do
            throw (IO.userError "Selected incidence exceeded proved polynomial")
          largest := max largest time
          count := count+1
  IO.println s!"Selected node incidence passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.SelectedIncidenceTests
