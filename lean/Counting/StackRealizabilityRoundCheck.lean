import Counting.StackRealizabilityRoundBuild
import Counting.StackRealizabilityRoundCleanup

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8000

def roundCheck : Routine 98 := sequence roundBuild (sequence roundConditionalGraph roundCleanup)

/-- One complete round of the compact certificate verifier, from the two
encoded input lists to the single accumulated Boolean. The field tables,
arc matrix, visited sets and arithmetic workspace are all constructed and
cleared by actual stack instructions. -/
theorem roundCheck_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (order round : Nat) (accepted : Bool) (tail : List Bool) (extra : Fin 3→List Bool) :
    ∃ time ≤ 1000000000000000000000000*(roundSize nodes values order round)^24,
      Executes roundCheck (roundFile (roundInputData nodes values order round (accepted::tail) extra)) time
        (roundFile (roundInputData nodes values order round
          ((accepted && roundComputedCheck nodes values order round)::tail) extra)) := by
  obtain ⟨buildTime,buildBound,building⟩ := roundBuild_executes nodes values length sorted order round accepted tail extra
  let arithmetic := accepted && roundNumericValue nodes values order round
  let built := roundComputedData nodes values order round (arithmetic::tail) extra
  obtain ⟨graphTime,graphBound,graphRun⟩ := roundConditionalGraph_executes built order arithmetic tail
    (by simp [built,roundComputedData,roundInputData])
    (by simp [built,roundComputedData,roundInputData])
  have tables : roundGraphTables built=roundComputedTables nodes values order round := by
    funext r
    fin_cases r <;> simp [roundGraphTables,built,roundComputedData,roundComputedTables]
  have width : built 7=List.replicate (nodes.length+1) true := by simp [built,roundComputedData]
  rw [tables,width,List.length_replicate] at graphRun
  have final : Function.update built 5
      ((arithmetic && (if 1<order then graphFieldsAnswer (roundComputedTables nodes values order round)
        (nodes.length+1) else true))::tail)=
      roundComputedData nodes values order round
        ((accepted && roundComputedCheck nodes values order round)::tail) extra := by
    funext r
    fin_cases r <;> simp [built,roundComputedData,roundInputData,arithmetic,roundComputedCheck,Bool.and_assoc]
  rw [final] at graphRun
  obtain ⟨clearTime,clearBound,clearing⟩ := roundCleanup_executes nodes values order round
    ((accepted && roundComputedCheck nodes values order round)::tail) extra
  rw [tables,width,roundComputedTables_size nodes values order round _ (by simp)] at graphBound
  let S := roundSize nodes values order round
  change buildTime ≤ 100000000000000000000*S^16 at buildBound
  change clearTime ≤ 12*(S^2+2) at clearBound
  have positive : 1 ≤ S := roundSize_positive nodes values order round
  have widthSmall : nodes.length+1 ≤ S := by dsimp only [S,roundSize];omega
  have widthSquare : (nodes.length+1)^2 ≤ S^2 := Nat.pow_le_pow_left widthSmall 2
  have linearSquare : S ≤ S^2 := Nat.le_self_pow (by decide) _
  have oneSquare : 1 ≤ S^2 := Nat.one_le_pow _ _ positive
  have graphBase : 7*(nodes.length+1)+2*(nodes.length+1)^2+1 ≤ 10*S^2 := by omega
  have graphLimit : graphTime ≤ 30000000000000000000000*S^24+30*(order.size+1)+2 := by
    have lifted := Nat.mul_le_mul_left 30000000000 (Nat.pow_le_pow_left graphBase 12)
    have raw := graphBound.trans (Nat.add_le_add_right (Nat.add_le_add_right lifted _) _)
    simpa only [roundGraph_scale] using raw
  have linear : S ≤ S^24 := Nat.le_self_pow (by decide) _
  have square : S^2 ≤ S^24 := Nat.pow_le_pow_right positive (by decide)
  have sixteenth : S^16 ≤ S^24 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^24 := Nat.one_le_pow _ _ positive
  have orderSmall : order.size+1 ≤ S := by dsimp only [S,roundSize];omega
  have execution := building.sequence (graphRun.sequence clearing)
  exact ⟨_,by change _ ≤ 1000000000000000000000000*S^24;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
