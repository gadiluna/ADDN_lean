import Counting.StackGaussianRead
import Counting.StackGaussianScalar
import Counting.StoredGaussianMatrixOperations

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

@[simp] theorem rational_neg_length (value : Rat) :
    (Encoding.rational.encode (-value)).length=(Encoding.rational.encode value).length := by
  simp [Encoding.rational_length]

/-- The arithmetic portion of an off-diagonal elimination. The factor is
retained for the separate, charged transcript emission. -/
abbrev eliminateArithmetic : Routine 50 := sequence readCoefficient (sequence negate add)

def eliminationConstant : Nat := 5001+(100000001+MatrixAxpy.costConstant)

theorem eliminateArithmetic_executes (rows : List (List Rat)) (target source : Fin rows.length)
    (value : Rat) (selected : rows[target.val][source.val]?=some value)
    (sameLength : rows[target.val].length=rows[source.val].length) (saved : Fin 10 → List Bool) :
    ∃ time ≤ eliminationConstant*(6*((Encoding.rationalMatrix.encode rows).length+rows.length+1))^16,
      Executes eliminateArithmetic
        (ready (Encoding.rationalMatrix.encode rows) [] (List.replicate (target.val+1) true)
          (List.replicate (source.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode (rows.set target.val
          (List.zipWith (fun a b => a+(-value)*b) rows[target.val] rows[source.val])))
          (Encoding.rational.encode (-value)) [] [] saved) := by
  obtain ⟨a,ha,ra⟩ := readCoefficient_executes rows target source.val value selected saved
  obtain ⟨b,hb,rb⟩ := negate_executes value (Encoding.rationalMatrix.encode rows)
    (List.replicate (target.val+1) true) (List.replicate (source.val+1) true) saved
  obtain ⟨c,hc,rc⟩ := add_executes (-value) rows target source sameLength saved
  have coefficient := RowScale.member_row_length_le rows[target.val] value (List.mem_of_getElem? selected)
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[target.val] (List.getElem_mem target.isLt)
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at rowBound
  let base := 6*((Encoding.rationalMatrix.encode rows).length+rows.length+1)
  have positive : 1 ≤ base := by dsimp [base];omega
  have indexBound := target.isLt
  have sourceBound := source.isLt
  have readBase : (Encoding.rationalMatrix.encode rows).length+target.val+source.val+3 ≤ base := by dsimp [base];omega
  have factorBase : (Encoding.rational.encode value).length+1 ≤ base := by dsimp [base];omega
  have operationBase : MatrixAxpy.sizeBound (-value) rows ≤ base := by
    simp only [MatrixAxpy.sizeBound,rational_neg_length];dsimp [base];omega
  have linear := Nat.le_self_pow (by decide : 16≠0) base
  have readBound : a ≤ 5000*base^16 := by omega
  have factorPower := Nat.pow_le_pow_left factorBase 3
  have higher := Nat.pow_le_pow_right positive (by decide : 3≤16)
  have scalarBound : b ≤ 100000000*base^16 := by omega
  have operationPower := Nat.mul_le_mul_left MatrixAxpy.costConstant (Nat.pow_le_pow_left operationBase 16)
  refine ⟨_,?_,ra.sequence (rb.sequence rc)⟩
  change a+1+(b+1+c) ≤ eliminationConstant*base^16
  have one : 1 ≤ base^16 := by exact one_le_pow₀ positive
  change _ ≤ ((5000+1)+((100000000+1)+MatrixAxpy.costConstant))*base^16
  simp only [Nat.add_mul,one_mul]
  exact Nat.add_le_add (Nat.add_le_add readBound one)
    (Nat.add_le_add (Nat.add_le_add scalarBound one) (hc.trans operationPower))

/-- Exact matrix component of the stored eliminator, without any assumption
about invertibility or earlier processed columns. The transcript is emitted
by the enclosing step after this arithmetic routine returns. -/
theorem eliminateArithmetic_augmented {q : Nat} (system : RationalSystem q) (target pivot : Fin q)
    (saved : Fin 10 → List Bool) :
    ∃ time ≤ eliminationConstant*(6*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+1))^16,
      Executes eliminateArithmetic
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) []
          (List.replicate (target.val+1) true) (List.replicate (pivot.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix
          (StoredGaussian.materialize (system.applyRowOp (.add target pivot (-system.coeff target pivot))))))
          (Encoding.rational.encode (-system.coeff target pivot)) [] [] saved) := by
  simpa only [StoredGaussian.add_augmentedMatrix,StoredGaussian.augmentedMatrix_getElem,
    StoredGaussian.augmentedMatrix_length] using
    eliminateArithmetic_executes (StoredGaussian.augmentedMatrix system)
      ⟨target.val,by simp [target.isLt]⟩ ⟨pivot.val,by simp [pivot.isLt]⟩ (system.coeff target pivot)
      (by simp [StoredGaussian.augmentedRow,pivot.isLt]) (by simp) saved

end Counting.StackMachine.GaussianBank
