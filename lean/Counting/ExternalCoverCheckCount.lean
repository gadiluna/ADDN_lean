import Counting.ExternalCoverSelectRow

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Compare the completed unary hit counter with one and conjoin the
result with the validity flag. The counter and comparison scratch are consumed. -/
def checkCount (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (pushBit (w 40) true)
    (sequence (ofProgram (Compare.equalityProgram (extra+46) (w 35) (w 40) (w 21)))
      (BooleanFold.single .conjunction (w 21) (w 1)))

theorem checkCount_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail) (temporary : store (w 40)=[]) :
    ∃ time ≤ (store (w 35)).length+15,
      Executes (checkCount extra w) store time
        (Function.update (Function.update store (w 35) []) (w 1)
          ((accepted && decide (store (w 35)=[true]))::tail)) := by
  let prepared := Function.update store (w 40) [true]
  have preparing : Executes (pushBit (w 40) true) store 1 prepared := by
    simpa [prepared,temporary] using pushBit_executes (w 40) true store
  have comparing := Compare.equality_executes (extra+46) (w 35) (w 40) (w 21)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) prepared
  let bit := decide (store (w 35)=[true])
  let compared := Function.update (Function.update (Function.update prepared (w 35) []) (w 40) []) (w 21)
    (bit::store (w 21))
  have compareAs : Executes (ofProgram (Compare.equalityProgram (extra+46) (w 35) (w 40) (w 21))) prepared
      (Compare.equalityCost (store (w 35)) [true]) compared := by
    simpa [prepared,compared,bit,w.injective.eq_iff] using comparing
  have folding := BooleanFold.single_executes .conjunction (w 21) (w 1)
    (by simp [w.injective.eq_iff]) compared bit accepted (store (w 21)) tail
    (by simp [compared]) (by simp [compared,prepared,w.injective.eq_iff,status])
  have final : BooleanFold.updated (w 21) (w 1) compared (store (w 21))
      (BooleanFold.operation .conjunction accepted bit) tail=
      Function.update (Function.update store (w 35) []) (w 1) ((accepted && bit)::tail) := by
    funext r
    by_cases e21 : r=w 21
    · subst r;simp [BooleanFold.updated,w.injective.eq_iff]
    · by_cases e40 : r=w 40
      · subst r;simp [BooleanFold.updated,compared,w.injective.eq_iff,temporary]
      · simp [BooleanFold.updated,BooleanFold.operation,compared,prepared,e21,e40,Function.update_apply]
  rw [final] at folding
  refine ⟨1+1+(Compare.equalityCost (store (w 35)) [true]+1+3),?_,preparing.sequence (compareAs.sequence folding)⟩
  have bound := Compare.equalityCost_le (store (w 35)) [true]
  simp only [List.length_cons,List.length_nil] at bound
  omega

end Counting.External.CoverVerification
