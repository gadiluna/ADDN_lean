import Counting.GaussianIntermediateRun

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem Counting.Executable
variable {q : Nat}

def integerEntries (system : RationalSystem q) : Augmented q ℤ :=
  fun row column => (augmented system row column).num

theorem integralSystem_integerEntries (system : RationalSystem q)
    (integral : ∀ row column, (augmented system row column).den = 1) :
    integralSystem (integerEntries system) = system := by
  have coefficients : (integralSystem (integerEntries system)).coeff = system.coeff := by
    ext row col
    exact Rat.coe_int_num_of_den_eq_one (integral row (some col))
  have rhs : (integralSystem (integerEntries system)).rhs = system.rhs := by
    ext row
    exact Rat.coe_int_num_of_den_eq_one (integral row none)
  exact congrArg₂ RationalSystem.mk coefficients rhs

/-- Public intermediate bound for the materialized Gaussian generator.
It applies to every integral square input, not only accepted systems. -/
theorem storedGaussian_integral_prefix_bits (system : RationalSystem q) (M : Nat)
    (integral : ∀ row column, (augmented system row column).den = 1)
    (bounded : ∀ row column, (augmented system row column).num.natAbs ≤ M)
    (length : Nat) (row : Fin q) (column : Option (Fin q)) :
    rationalBits (augmented (StoredGaussian.replay system
      ((StoredGaussian.runGaussian system).opsRev.reverse.take length)) row column) ≤ intermediateBound q M := by
  have result := storedGaussian_replay_prefix_bits (integerEntries system) M bounded length row column
  simpa only [integralSystem_integerEntries system integral] using result

theorem storedGaussian_integral_operation_bits (system : RationalSystem q) (M : Nat)
    (integral : ∀ row column, (augmented system row column).den = 1)
    (bounded : ∀ row column, (augmented system row column).num.natAbs ≤ M) (op : RowOp q)
    (emitted : op ∈ (StoredGaussian.runGaussian system).opsRev) :
    OperationBound (intermediateBound q M) op := by
  have same := integralSystem_integerEntries system integral
  have result := storedGaussian_operation_bits (integerEntries system) M bounded op
  rw [same] at result
  exact result emitted

theorem normalSystem_augmented_integral_bounded (width : Nat) (rows : List Equation) (M : Nat)
    (coeffIntegral : ∀ r i, (rowMatrix width rows r i).den = 1)
    (rhsIntegral : ∀ r, (rowRhs rows r).den = 1)
    (coeffBound : ∀ r i, (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhsBound : ∀ r, (rowRhs rows r).num.natAbs ≤ M) :
    (∀ row column, (augmented (normalSystem width rows) row column).den = 1) ∧
    (∀ row column, (augmented (normalSystem width rows) row column).num.natAbs ≤ rows.length*M^2) := by
  obtain ⟨coeff, rhs⟩ := integer_normal_bounds width rows M coeffBound rhsBound
  have coefficients := normal_coeff_cast width rows coeffIntegral
  have vector := normal_rhs_cast width rows coeffIntegral rhsIntegral
  constructor
  · intro row column
    cases column <;> simp only [augmented, coefficients, vector, Matrix.map_apply, Rat.den_intCast]
  · intro row column
    cases column with
    | none => simpa only [augmented, vector, Rat.num_intCast] using rhs row
    | some col => simpa only [augmented, coefficients, Matrix.map_apply, Rat.num_intCast] using coeff row col

/-- This is the actual normal-equation system used by solveLinear?. No
successful-answer premise is required: singular and rejected candidates
have the same bound on every generated/replayed intermediate. -/
theorem normalSystem_all_intermediate_bits (width : Nat) (rows : List Equation) (M : Nat)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧ (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M)
    (length : Nat) (row : Fin width) (column : Option (Fin width)) :
    rationalBits (augmented (StoredGaussian.replay (normalSystem width rows)
      ((StoredGaussian.runGaussian (normalSystem width rows)).opsRev.reverse.take length)) row column) ≤
      intermediateBound width (rows.length*M^2) := by
  obtain ⟨integral, bounded⟩ := normalSystem_augmented_integral_bounded width rows M
    (fun r i => (coeff r i).1) (fun r => (rhs r).1) (fun r i => (coeff r i).2) (fun r => (rhs r).2)
  exact storedGaussian_integral_prefix_bits _ _ integral bounded length row column

theorem normalSystem_all_operation_bits (width : Nat) (rows : List Equation) (M : Nat)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧ (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M)
    (op : RowOp width) (emitted : op ∈ (StoredGaussian.runGaussian (normalSystem width rows)).opsRev) :
    OperationBound (intermediateBound width (rows.length*M^2)) op := by
  obtain ⟨integral, bounded⟩ := normalSystem_augmented_integral_bounded width rows M
    (fun r i => (coeff r i).1) (fun r => (rhs r).1) (fun r i => (coeff r i).2) (fun r => (rhs r).2)
  exact storedGaussian_integral_operation_bits _ _ integral bounded op emitted

end Counting.GaussianBits
