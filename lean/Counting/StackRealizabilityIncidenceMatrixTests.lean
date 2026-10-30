import Counting.StackRealizabilityIncidenceMatrix
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.IncidenceMatrixTests
open Routine

def tests : IO Unit := do
  let cases : List (List Executable.Node) := [[],[⟨0,none,true,0,[]⟩],
    [⟨0,none,true,1,[]⟩,⟨1,some 0,false,1,[(0,1)]⟩],
    [⟨0,some 2,false,7,[(0,0),(0,5),(2,3)]⟩,⟨4,none,true,0,[(1,2)]⟩]]
  let mut largest := 0
  let mut count := 0
  for nodes in cases do
    for accepted in [false,true] do
      let source := Encoding.sequence Encoding.node nodes ++ [true,false,false]
      let width := List.replicate nodes.length true
      let status := [accepted,false,true]
      let store := incidenceTableFile source [] [] [] [] status width [] []
      let incoming := (List.range (nodes.length+1)).flatMap (fun x =>
        (List.range (nodes.length+1)).map (fun y => decide (0 < Executable.countFrom (nodes[x]?.getD default) y)))
      let parent := (List.range (nodes.length+1)).flatMap (fun x =>
        (List.range (nodes.length+1)).map (fun y => decide ((nodes[x]?.getD default).parent=some y)))
      let expected := Function.update (Function.update
        (incidenceTableFile source [] [] [] [] status (false::width) [] []) 0 incoming) 1 parent
      let program := incidenceMatrix.program
      match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none => throw (IO.userError "Incidence matrix exhausted test fuel")
      | some (time,result) =>
        unless (List.finRange 46).all (fun r => result.store r == expected r) do
          throw (IO.userError "Incidence matrix violated row-major full-store contract")
        unless time ≤ 40000*(source.length+width.length+2)^8 do
          throw (IO.userError "Incidence matrix exceeded proved polynomial")
        largest := max largest time
        count := count+1
  IO.println s!"Incidence matrices passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.IncidenceMatrixTests
