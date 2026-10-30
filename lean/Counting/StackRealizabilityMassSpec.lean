import Counting.StackRealizabilityMassCalculate
import Counting.DagSemanticsInjective

namespace Counting.StackMachine.RealizabilityCheck
open Routine

/-- A successful syntax check supplies exactly the sparse-order premise used
by the demand scan; the initial-level case has an empty incoming list. -/
theorem mass_sorted_of_valid (vista : Executable.Vista) (valid : vista.valid=true)
    (index : Nat) (inside : index<vista.nodes.size) :
    Executable.countsSorted (vista.node index).incoming=true := by
  have checked := Executable.nodeValid_of_valid vista valid index inside
  by_cases zero : (vista.node index).level=0
  · have empty := (Executable.nodeValid_zero vista index checked zero).2.2
    simp [empty,Executable.countsSorted]
  · obtain ⟨_,_,_,_,_,sorted,_⟩ := Executable.nodeValid_positive vista index checked zero
    exact sorted

/-- The actual three numerical clauses of the compact verifier, calculated
from binary encodings and preserving both complete input lists. -/
theorem massCalculate_actual (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (source weightWord : List Bool) (accepted : Bool) (tail nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode vista.nodes.toList++nodeSuffix)
    (weightInput : weightWord=(Encoding.list Encoding.natural).encode weights.toList++weightSuffix)
    (round old : Nat) :
    ∃ time ≤ 100000000*(source.length+weightWord.length+(round+1).size+old.size+2)^15,
      Executes massCalculate
        (massFile source weightWord (round+1).bits [] old.bits (accepted::tail) [] [] []) time
        (massFile source weightWord (round+1).bits [] old.bits (accepted::tail)
          (RealizabilityVerifier.childCount vista weights round old).bits
          (RealizabilityVerifier.demand vista weights round old).bits
          (RealizabilityVerifier.supply vista weights round old).bits) := by
  have sortedAt := mass_sorted_of_valid vista valid
  have sorted (node : Executable.Node) (member : node∈vista.nodes.toList) :
      Executable.countsSorted node.incoming=true := by
    obtain ⟨index,inside,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    simpa [Executable.Vista.node,inside] using sortedAt index inside
  simpa only [childRangeSum_vista vista weights round old length,
    supplyRangeSum_vista vista weights round old length,
    demandRangeSum_vista vista weights round old length sortedAt] using
    massCalculate_executes source weightWord accepted tail vista.nodes.toList sorted weights.toList
      (by simpa only [Array.length_toList] using length) nodeSuffix weightSuffix
      nodeInput weightInput (round+1) old

end Counting.StackMachine.RealizabilityCheck
