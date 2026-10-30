import Counting.StackRealizabilityRoundCheck
import Counting.RealizabilityRoundCheckSpec
import Counting.StackRealizabilityLevelVisible

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier RealizabilityVerifier.CompactGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem roundComputedTables_actual (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) (N r : Nat) :
    roundComputedTables vista.nodes.toList weights.toList N r=
      graphTablesOfFields (actualFields N vista weights r) := by
  have visible : roundVisibleValue vista.nodes.toList weights.toList r=
      ((Executable.levelNodes vista (r+1)).map (weight weights)).sum :=
    levelRangeSum_vista vista weights (r+1) length
  funext i
  fin_cases i
  · exact maskSlots_new_values N vista weights r
  · exact maskSlots_old_values N vista weights r
  · change List.replicate vista.nodes.toList.length false++
      [decide (0<N-roundVisibleValue vista.nodes.toList weights.toList r)]=_
    rw [Array.length_toList,visible]
    exact maskSlots_outside_values N vista weights r
  · exact maskSlots_degree_values N vista weights r
  · change leavingRangeValues vista.nodes.toList weights.toList (r+1) 0 (vista.nodes.toList.length+1)=
      vectorBits (actualFields N vista weights r).leavingPositive
    simpa only [Array.length_toList] using
      leavingRangeValues_actual N vista weights length r
  · change deficitRangeValues vista.nodes.toList weights.toList (r+1) 0 (vista.nodes.toList.length+1)=
      vectorBits (actualFields N vista weights r).deficitPositive
    simpa only [Array.length_toList] using
      deficitRangeValues_actual N vista weights valid length r
  · exact parentMatrixValues_actual N vista weights r
  · exact incomingMatrixValues_actual N vista weights r

theorem roundComputedCheck_actual (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) (N r : Nat) :
    roundComputedCheck vista.nodes.toList weights.toList N r=checkedRound vista weights N r := by
  unfold roundComputedCheck roundNumericValue checkedRound
  rw [roundComputedTables_actual vista weights valid length,Array.length_toList,graphFieldsAnswer_actual,
    maskSlots_old_values N vista weights r]
  dsimp only [roundVisibleValue]
  rw [levelRangeSum_vista vista weights (r+1) length]

/-- The runtime subroutine checks exactly the original verifier's arithmetic
and connectivity clauses for this round, with binary multiplicities and
without constructing an order-N physical realization. -/
theorem roundCheck_actual (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (N r : Nat) (accepted : Bool) (tail : List Bool) (extra : Fin 3→List Bool) :
    ∃ time ≤ 1000000000000000000000000*(roundSize vista.nodes.toList weights.toList N r)^24,
      Executes roundCheck
        (roundFile (roundInputData vista.nodes.toList weights.toList N r (accepted::tail) extra)) time
        (roundFile (roundInputData vista.nodes.toList weights.toList N r
          ((accepted && checkedRound vista weights N r)::tail) extra)) := by
  have sorted (node : Executable.Node) (member : node∈vista.nodes.toList) :
      Executable.countsSorted node.incoming=true := by
    obtain ⟨index,inside,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    simpa [Executable.Vista.node,inside] using mass_sorted_of_valid vista valid index inside
  simpa only [roundComputedCheck_actual vista weights valid length N r] using
    roundCheck_executes vista.nodes.toList weights.toList
      (by simpa only [Array.length_toList] using length) sorted N r accepted tail extra

end Counting.StackMachine.RealizabilityCheck
