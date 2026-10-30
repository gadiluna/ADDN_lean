import Counting.StackRealizabilityRoundCorrectness

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000

def roundItem : Routine 98 := sequence roundCheck (DagValidation.incrementRoutine 97 0 83 2)

theorem roundItem_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (N r : Nat) (accepted : Bool) (tail : List Bool) (extra : Fin 3→List Bool) :
    ∃ time ≤ 2000000000000000000000000*(roundSize vista.nodes.toList weights.toList N r)^24,
      Executes roundItem
        (roundFile (roundInputData vista.nodes.toList weights.toList N r (accepted::tail) extra)) time
        (roundFile (roundInputData vista.nodes.toList weights.toList N (r+1)
          ((accepted && checkedRound vista weights N r)::tail) extra)) := by
  obtain ⟨checkTime,checkBound,checkRun⟩ := roundCheck_actual vista weights valid length N r accepted tail extra
  let result := (accepted && checkedRound vista weights N r)::tail
  let ready := roundFile (roundInputData vista.nodes.toList weights.toList N r result extra)
  obtain ⟨incrementTime,incrementBound,incrementing⟩ := DagValidation.increment_natural 97 0 83 2
    (by decide) (by decide) (by decide) ready (by simp [ready,roundFile]) (by simp [ready,roundFile])
    r (by simp [ready,roundFile,roundInputData])
  have final : Function.update ready 83 (r+1).bits=
      roundFile (roundInputData vista.nodes.toList weights.toList N (r+1) result extra) := by
    change Function.update (roundFile _) (roundContext 3) (r+1).bits=_
    rw [roundFile_update]
    congr 1
    funext i
    fin_cases i <;> simp [roundInputData]
  rw [final] at incrementing
  let S := roundSize vista.nodes.toList weights.toList N r
  change checkTime ≤ 1000000000000000000000000*S^24 at checkBound
  have linear : S ≤ S^24 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^24 := Nat.one_le_pow _ _ (roundSize_positive _ _ _ _)
  have rSmall : r.size ≤ S := by dsimp only [S,roundSize];omega
  have execution := checkRun.sequence incrementing
  exact ⟨_,by change _ ≤ 2000000000000000000000000*S^24;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
