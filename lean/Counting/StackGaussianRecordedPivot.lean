import Counting.StackGaussianRecord
import Counting.StackGaussianNormalizationArithmetic

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

abbrev swapRecorded : Routine 50 := sequence (loadPair 0 2) (sequence swap recordSwap)
abbrev normalizeRecorded : Routine 50 := sequence (loadPair 0 0)
  (sequence normalizeArithmetic (sequence recordScale (clear 0)))

def recordedSwapCost {q : Nat} (system : RationalSystem q) (pivot row : Fin q) : Nat :=
  (5*(pivot.val+1)+5*(row.val+1)+5)+1+
    (100*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)+1+
      200*(pivot.val+row.val+15)^2)

theorem swapRecorded_executes {q : Nat} (state : GaussianState q) (pivot row : Fin q) :
    ∃ time ≤ recordedSwapCost state.system pivot row,
      Executes swapRecorded (stateStore state pivot.val (List.replicate (row.val+1) true) [] [] []) time
        (stateStore (StoredGaussian.emit state (.swap pivot row)) pivot.val (List.replicate (row.val+1) true) [] [] []) := by
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)
  let updated := StoredGaussian.emit state (.swap pivot row)
  let result := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix updated.system)
  let saved := stateSaved state pivot.val (List.replicate (row.val+1) true) [] [] []
  have loaded := loadPair_executes 0 2 matrix [] saved
  change Executes (loadPair 0 2) (ready matrix [] [] [] saved)
    (5*(List.replicate (pivot.val+1) true).length+5*(List.replicate (row.val+1) true).length+5)
    (ready matrix [] (List.replicate (pivot.val+1) true) (List.replicate (row.val+1) true) saved) at loaded
  simp only [List.length_replicate] at loaded
  obtain ⟨swapTime,swapBound,swapped⟩ := swap_executes (StoredGaussian.augmentedMatrix state.system)
    ⟨pivot.val,by simp [pivot.isLt]⟩ ⟨row.val,by simp [row.isLt]⟩ [] saved
  have resultMatrix : result=Encoding.rationalMatrix.encode
      (((StoredGaussian.augmentedMatrix state.system).set pivot.val (StoredGaussian.augmentedRow state.system row)).set
        row.val (StoredGaussian.augmentedRow state.system pivot)) := by
    dsimp [result,updated,StoredGaussian.emit]
    rw [StoredGaussian.swap_augmentedMatrix]
  simp only [StoredGaussian.augmentedMatrix_getElem] at swapped
  rw [←resultMatrix] at swapped
  obtain ⟨recordTime,recordBound,recorded⟩ := recordSwap_executes result [] pivot.val row.val saved rfl rfl
  have finalSaved : logSaved saved (.swap pivot.val row.val)=
      stateSaved updated pivot.val (List.replicate (row.val+1) true) [] [] [] :=
    logSaved_stateSaved state pivot.val (List.replicate (row.val+1) true) [] [] [] (.swap pivot row)
  rw [finalSaved] at recorded
  refine ⟨_,?_,loaded.sequence (swapped.sequence recorded)⟩
  unfold recordedSwapCost
  exact Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right swapBound 1) recordBound) _

def recordedScaleCost {q : Nat} (system : RationalSystem q) (pivot : Fin q) : Nat :=
  let factor := Encoding.rational.encode (system.coeff pivot pivot)⁻¹
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)
  (10*(pivot.val+1)+5)+1+
    (70000000000*(6*(matrix.length+q+1))^4+1+
      (200*(pivot.val+factor.length+10)^2+1+(factor.length+1)))

theorem normalizeRecorded_executes {q : Nat} (state : GaussianState q) (pivot : Fin q)
    (candidate row counter : List Bool) :
    ∃ time ≤ recordedScaleCost state.system pivot,
      Executes normalizeRecorded (stateStore state pivot.val candidate row counter []) time
        (stateStore (StoredGaussian.emit state (.scale pivot (state.system.coeff pivot pivot)⁻¹))
          pivot.val candidate row counter []) := by
  let factor := Encoding.rational.encode (state.system.coeff pivot pivot)⁻¹
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)
  let operation : RowOp q := .scale pivot (state.system.coeff pivot pivot)⁻¹
  let updated := StoredGaussian.emit state operation
  let result := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix updated.system)
  let saved := stateSaved state pivot.val candidate row counter []
  have loaded := loadPair_executes 0 0 matrix [] saved
  change Executes (loadPair 0 0) (ready matrix [] [] [] saved)
    (5*(List.replicate (pivot.val+1) true).length+5*(List.replicate (pivot.val+1) true).length+5)
    (ready matrix [] (List.replicate (pivot.val+1) true) (List.replicate (pivot.val+1) true) saved) at loaded
  simp only [List.length_replicate] at loaded
  obtain ⟨arithmeticTime,arithmeticBound,arithmetic⟩ := normalizeArithmetic_augmented state.system pivot saved
  change Executes normalizeArithmetic _ arithmeticTime (ready result factor [] [] saved) at arithmetic
  obtain ⟨recordTime,recordBound,recorded⟩ := recordScale_executes result (state.system.coeff pivot pivot)⁻¹ pivot.val saved rfl
  change Executes recordScale (ready result factor [] [] saved) recordTime
    (ready result factor [] [] (logSaved saved (RawRowOp.ofRowOp operation))) at recorded
  have erased := clearFactor_executes result factor [] [] (logSaved saved (RawRowOp.ofRowOp operation))
  have finalSaved : logSaved saved (RawRowOp.ofRowOp operation)=
      stateSaved updated pivot.val candidate row counter [] :=
    logSaved_stateSaved state pivot.val candidate row counter [] operation
  rw [finalSaved] at erased
  have combined := loaded.sequence (arithmetic.sequence (recorded.sequence (by simpa only [finalSaved] using erased)))
  refine ⟨_,?_,combined⟩
  have loadedTime : 5*(pivot.val+1)+5*(pivot.val+1)+5=10*(pivot.val+1)+5 := by omega
  rw [loadedTime]
  unfold recordedScaleCost
  exact Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right arithmeticBound 1)
    (Nat.add_le_add_right (Nat.add_le_add_right recordBound 1) (factor.length+1))) _

end Counting.StackMachine.GaussianBank
