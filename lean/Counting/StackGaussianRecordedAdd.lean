import Counting.StackGaussianRecord
import Counting.StackGaussianEliminationArithmetic

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

abbrev eliminateRecorded : Routine 50 := sequence (loadPair 6 0)
  (sequence eliminateArithmetic (sequence recordAdd (clear 0)))

def recordedAddCost {q : Nat} (system : RationalSystem q) (target pivot : Fin q) : Nat :=
  let factor := Encoding.rational.encode (-system.coeff target pivot)
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)
  (5*(target.val+1)+5*(pivot.val+1)+5)+1+
    (eliminationConstant*(6*(matrix.length+q+1))^16+1+
      (200*(target.val+pivot.val+factor.length+10)^2+1+(factor.length+1)))

/-- One complete emitted row addition: copying indices, coefficient lookup,
negation, matrix update, canonical transcript emission and factor cleanup.
The result is the complete stored state, including `opsRev`, not a projection. -/
theorem eliminateRecorded_executes {q : Nat} (state : GaussianState q) (target pivot : Fin q)
    (counter : List Bool) :
    ∃ time ≤ recordedAddCost state.system target pivot,
      Executes eliminateRecorded
        (stateStore state pivot.val [] (List.replicate (target.val+1) true) counter []) time
        (stateStore (StoredGaussian.emit state (.add target pivot (-state.system.coeff target pivot)))
          pivot.val [] (List.replicate (target.val+1) true) counter []) := by
  let factor := Encoding.rational.encode (-state.system.coeff target pivot)
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)
  let operation : RowOp q := .add target pivot (-state.system.coeff target pivot)
  let updated := StoredGaussian.emit state operation
  let result := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix updated.system)
  let saved := stateSaved state pivot.val [] (List.replicate (target.val+1) true) counter []
  have loaded := loadPair_executes 6 0 matrix [] saved
  change Executes (loadPair 6 0) (ready matrix [] [] [] saved)
    (5*(List.replicate (target.val+1) true).length+5*(List.replicate (pivot.val+1) true).length+5)
    (ready matrix [] (List.replicate (target.val+1) true) (List.replicate (pivot.val+1) true) saved) at loaded
  simp only [List.length_replicate] at loaded
  obtain ⟨arithmeticTime,arithmeticBound,arithmetic⟩ := eliminateArithmetic_augmented state.system target pivot saved
  change Executes eliminateArithmetic _ arithmeticTime (ready result factor [] [] saved) at arithmetic
  obtain ⟨recordTime,recordBound,recorded⟩ := recordAdd_executes result (-state.system.coeff target pivot)
    target.val pivot.val saved rfl rfl
  change Executes recordAdd (ready result factor [] [] saved) recordTime
    (ready result factor [] [] (logSaved saved (RawRowOp.ofRowOp operation))) at recorded
  have erased := clearFactor_executes result factor [] [] (logSaved saved (RawRowOp.ofRowOp operation))
  have finalSaved : logSaved saved (RawRowOp.ofRowOp operation)=
      stateSaved updated pivot.val [] (List.replicate (target.val+1) true) counter [] :=
    logSaved_stateSaved state pivot.val [] (List.replicate (target.val+1) true) counter [] operation
  rw [finalSaved] at erased
  have combined := loaded.sequence (arithmetic.sequence (recorded.sequence (by simpa only [finalSaved] using erased)))
  refine ⟨_,?_,combined⟩
  unfold recordedAddCost
  exact Nat.add_le_add_left (Nat.add_le_add
    (Nat.add_le_add_right arithmeticBound 1)
    (Nat.add_le_add_right (Nat.add_le_add_right recordBound 1) (factor.length+1))) _

end Counting.StackMachine.GaussianBank
