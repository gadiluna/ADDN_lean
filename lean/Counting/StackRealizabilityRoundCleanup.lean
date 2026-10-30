import Counting.StackRealizabilityRoundCost
import Counting.StackRoutineClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

/-- The erasure cost needs a bound only on cells actually selected for
clearing; preserved input and outer-loop cells may contain arbitrary words. -/
theorem clearSelected_executes {registers : Nat} (selected : List (Fin (registers+2)))
    (store : Store registers) (bound : Nat)
    (bounded : ∀r∈selected,(store r).length ≤ bound) :
    ∃ time ≤ selected.length*(bound+2),
      Executes (clearRegisters selected) store time (clearedStore selected store) := by
  induction selected generalizing store with
  | nil => exact ⟨0,by simp,skip_executes store⟩
  | cons r rest ih =>
    have clearing := clear_executes r store
    have tailBound (i : Fin (registers+2)) (member : i∈rest) :
        (Function.update store r [] i).length ≤ bound := by
      by_cases same : i=r
      · simp [same]
      · simpa [same] using bounded i (by simp [member])
    obtain ⟨time,timeBound,tailRun⟩ := ih (Function.update store r []) tailBound
    have final : clearedStore rest (Function.update store r [])=clearedStore (r::rest) store := by
      funext i
      by_cases same : i=r <;> by_cases member : i∈rest <;> simp [clearedStore,same,member]
    rw [final] at tailRun
    have headBound := bounded r (by simp)
    exact ⟨_,by simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega,clearing.sequence tailRun⟩

def roundWork : List (Fin 100) := [84,86,87,88,89,90,91,92,93,94,95,96]
def roundCleanup : Routine 98 := clearRegisters roundWork

theorem roundCleanup_executes (nodes : List Executable.Node) (values : List Nat) (order round : Nat)
    (status : List Bool) (extra : Fin 3→List Bool) :
    ∃ time ≤ 12*((roundSize nodes values order round)^2+2),
      Executes roundCleanup (roundFile (roundComputedData nodes values order round status extra)) time
        (roundFile (roundInputData nodes values order round status extra)) := by
  let S := roundSize nodes values order round
  have positive : 1 ≤ S := roundSize_positive nodes values order round
  have linear : S ≤ S^2 := Nat.le_self_pow (by decide) _
  have nodeWord : ((Encoding.list Encoding.node).encode nodes).length ≤ S := by
    dsimp only [S,roundSize,massInputSize];omega
  have nodeSequence : (Encoding.sequence Encoding.node nodes).length ≤ S := by
    have smaller : (Encoding.sequence Encoding.node nodes).length ≤ ((Encoding.list Encoding.node).encode nodes).length := by
      change _ ≤ (Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes).length
      simp only [List.length_append];omega
    exact smaller.trans nodeWord
  have widthSmall : nodes.length+1 ≤ S := by dsimp only [S,roundSize];omega
  have matrixSmall : (nodes.length+1)^2 ≤ S^2 := Nat.pow_le_pow_left widthSmall 2
  have successorSize : (round+1).size ≤ S := by
    have bounded : (round+1).size ≤ round.size+1 :=
      (Nat.size_le_size (Nat.succ_le_of_lt (Nat.lt_size_self round))).trans_eq Nat.size_pow
    dsimp only [S,roundSize];omega
  have visibleSmall : (roundVisibleValue nodes values round).size ≤ S :=
    (roundVisibleValue_size nodes values round).trans (by dsimp only [S,roundSize];omega)
  have bounded (r : Fin 100) (member : r∈roundWork) :
      (roundFile (roundComputedData nodes values order round status extra) r).length ≤ S^2 := by
    simp [roundWork] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [roundFile,roundComputedData,roundComputedTables,Encoding.bits_length]
    all_goals omega
  obtain ⟨time,bound,run⟩ := clearSelected_executes roundWork
    (roundFile (roundComputedData nodes values order round status extra)) (S^2) bounded
  have final : clearedStore roundWork (roundFile (roundComputedData nodes values order round status extra))=
      roundFile (roundInputData nodes values order round status extra) := by
    funext r
    fin_cases r <;> simp [clearedStore,roundWork,roundFile,roundComputedData,roundInputData]
  rw [final] at run
  exact ⟨time,by simpa [roundWork] using bound,run⟩

end Counting.StackMachine.RealizabilityCheck
