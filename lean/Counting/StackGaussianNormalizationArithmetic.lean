import Counting.StackGaussianEliminationArithmetic

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

@[simp] theorem rational_inv_length (value : Rat) :
    (Encoding.rational.encode value⁻¹).length=(Encoding.rational.encode value).length := by
  by_cases zero : value=0
  · simp [zero]
  · have numerator : value.num≠0 := by simpa using zero
    simp [Encoding.rational_length,Rat.num_inv,Rat.den_inv,numerator,Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero numerator,Nat.add_comm]

theorem clearSecond_executes (matrix factor first second : List Bool) (saved : Fin 10 → List Bool) :
    Executes (clear (39 : Fin 52)) (ready matrix factor first second saved) (second.length+1)
      (ready matrix factor first [] saved) := by
  have ran := clear_executes (39 : Fin 52) (ready matrix factor first second saved)
  change Executes _ _ (second.length+1) _ at ran
  convert ran using 1
  funext r;fin_cases r <;> simp [ready,bank,MatrixAxpy.file,RowAxpy.file]

/-- Normalize one diagonal entry after a pivot swap. The computed inverse
remains in register zero so the exact scale operation can be recorded. -/
abbrev normalizeArithmetic : Routine 50 := sequence readCoefficient
  (sequence inverse (sequence (clear 39) scale))

theorem normalizeArithmetic_executes (rows : List (List Rat)) (pivot : Fin rows.length) (value : Rat)
    (selected : rows[pivot.val][pivot.val]?=some value) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 70000000000*(6*((Encoding.rationalMatrix.encode rows).length+rows.length+1))^4,
      Executes normalizeArithmetic
        (ready (Encoding.rationalMatrix.encode rows) [] (List.replicate (pivot.val+1) true)
          (List.replicate (pivot.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode (rows.set pivot.val (rows[pivot.val].map (value⁻¹*·))))
          (Encoding.rational.encode value⁻¹) [] [] saved) := by
  obtain ⟨a,ha,ra⟩ := readCoefficient_executes rows pivot pivot.val value selected saved
  obtain ⟨b,hb,rb⟩ := inverse_executes value (Encoding.rationalMatrix.encode rows)
    (List.replicate (pivot.val+1) true) (List.replicate (pivot.val+1) true) saved
  have rc := clearSecond_executes (Encoding.rationalMatrix.encode rows) (Encoding.rational.encode value⁻¹)
    (List.replicate (pivot.val+1) true) (List.replicate (pivot.val+1) true) saved
  obtain ⟨d,hd,rd⟩ := scale_executes value⁻¹ rows pivot saved
  have coefficient := RowScale.member_row_length_le rows[pivot.val] value (List.mem_of_getElem? selected)
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[pivot.val] (List.getElem_mem pivot.isLt)
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at rowBound
  let base := 6*((Encoding.rationalMatrix.encode rows).length+rows.length+1)
  have positive : 1 ≤ base := by dsimp [base];omega
  have indexBound := pivot.isLt
  have readBase : (Encoding.rationalMatrix.encode rows).length+pivot.val+pivot.val+3 ≤ base := by dsimp [base];omega
  have factorBase : (Encoding.rational.encode value).length+1 ≤ base := by dsimp [base];omega
  have scaleBase : 2*(Encoding.rational.encode value⁻¹).length+(Encoding.rationalMatrix.encode rows).length+2 ≤ base := by
    rw [rational_inv_length];dsimp [base];omega
  have linear := Nat.le_self_pow (by decide : 4≠0) base
  have readBound : a ≤ 5000*base^4 := by omega
  have factorPower := Nat.pow_le_pow_left factorBase 3
  have higher := Nat.pow_le_pow_right positive (by decide : 3≤4)
  have scalarBound : b ≤ 100000000*base^4 := by omega
  have scalePower := Nat.pow_le_pow_left scaleBase 4
  have indexBase : pivot.val+2 ≤ base := by dsimp [base];omega
  have indexPower : pivot.val+2 ≤ base^4 := indexBase.trans linear
  have one : 1 ≤ base^4 := one_le_pow₀ positive
  refine ⟨_,?_,ra.sequence (rb.sequence (rc.sequence rd))⟩
  simp only [List.length_replicate]
  change a+1+(b+1+(pivot.val+1+1+1+d)) ≤ 70000000000*base^4
  omega

theorem normalizeArithmetic_augmented {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (saved : Fin 10 → List Bool) :
    ∃ time ≤ 70000000000*(6*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+1))^4,
      Executes normalizeArithmetic
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) []
          (List.replicate (pivot.val+1) true) (List.replicate (pivot.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix
          (StoredGaussian.materialize (system.applyRowOp (.scale pivot (system.coeff pivot pivot)⁻¹)))))
          (Encoding.rational.encode (system.coeff pivot pivot)⁻¹) [] [] saved) := by
  simpa only [StoredGaussian.scale_augmentedMatrix,StoredGaussian.augmentedMatrix_getElem,
    StoredGaussian.augmentedMatrix_length] using
    normalizeArithmetic_executes (StoredGaussian.augmentedMatrix system)
      ⟨pivot.val,by simp [pivot.isLt]⟩ (system.coeff pivot pivot)
      (by simp [StoredGaussian.augmentedRow,pivot.isLt]) saved

end Counting.StackMachine.GaussianBank
