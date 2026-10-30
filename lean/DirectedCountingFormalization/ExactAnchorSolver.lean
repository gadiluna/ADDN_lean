import DirectedCountingFormalization.LastNonbranchRecognizer
import DirectedCountingFormalization.MatrixUniqueness
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact normalized solver for a nonbranching anchor

For the rational balance matrix `L = M - D`, the normalized eigenvector is
the unique solution of

`(Lᵀ L + eℓ eℓᵀ) x = eℓ`,

where `ℓ` is the leader coordinate.  This formulation keeps every balance
row and avoids selecting a possibly singular minor.  The matrix on the left
is nonsingular: its quadratic energy is the sum of the squares of `L x` and
the leader coordinate, while strong connectivity makes `ker L`
one-dimensional.

The executable solution in this file is Cramer's rule over `ℚ`.  Its
correctness and conversion back to `ℕ` are kernel checked.  Mathlib's
determinant evaluator expands over permutations, so this file deliberately
does not claim a polynomial running-time bound for the current evaluator.
-/

set_option warningAsError true

namespace DirectedCounting
namespace ExactAnchorSolver

open scoped BigOperators Matrix

variable {q candidate : Nat}

/-- Rational form of `M - D`. -/
def residualMatrix (A : IntegralAnchorInstance q) :
    Matrix (Fin q) (Fin q) ℚ :=
  fun i j ↦ (A.multiplicity i j : ℚ) -
    if i = j then (A.degree i : ℚ) else 0

/-- Rank-one projector onto the normalized leader coordinate. -/
def leaderProjector (A : IntegralAnchorInstance q) :
    Matrix (Fin q) (Fin q) ℚ :=
  fun i j ↦ if i = A.leader then
    if j = A.leader then 1 else 0
  else 0

/-- The nonsingular normal-equation matrix. -/
def normalMatrix (A : IntegralAnchorInstance q) :
    Matrix (Fin q) (Fin q) ℚ :=
  (residualMatrix A)ᵀ * residualMatrix A + leaderProjector A

/-- Right-hand side enforcing leader normalization. -/
def normalizedRhs (A : IntegralAnchorInstance q) : Fin q → ℚ :=
  fun i ↦ if i = A.leader then 1 else 0

theorem residualMatrix_mulVec_apply
    (A : IntegralAnchorInstance q) (x : Fin q → ℚ) (i : Fin q) :
    (residualMatrix A *ᵥ x) i =
      (∑ j, (A.multiplicity i j : ℚ) * x j) -
        (A.degree i : ℚ) * x i := by
  classical
  simp only [residualMatrix, Matrix.mulVec, dotProduct]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

theorem leaderProjector_mulVec
    (A : IntegralAnchorInstance q) (x : Fin q → ℚ) :
    leaderProjector A *ᵥ x =
      fun i ↦ if i = A.leader then x A.leader else 0 := by
  classical
  funext i
  by_cases hi : i = A.leader
  · subst i
    simp [leaderProjector, Matrix.mulVec, dotProduct]
  · simp [leaderProjector, Matrix.mulVec, dotProduct, hi]

/-- Quadratic energy of the normal matrix. -/
theorem dotProduct_normalMatrix_mulVec
    (A : IntegralAnchorInstance q) (x : Fin q → ℚ) :
    x ⬝ᵥ (normalMatrix A *ᵥ x) =
      (residualMatrix A *ᵥ x) ⬝ᵥ (residualMatrix A *ᵥ x) +
        x A.leader * x A.leader := by
  classical
  rw [normalMatrix, Matrix.add_mulVec, dotProduct_add,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    leaderProjector_mulVec]
  simp [dotProduct]

/-- The checked integral anchor vector lies in the rational kernel of
`M - D`. -/
theorem residualMatrix_mulVec_natCast_eq_zero
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    residualMatrix A *ᵥ (fun i ↦ (output.weight i : ℚ)) = 0 := by
  funext i
  rw [residualMatrix_mulVec_apply]
  have hbalance :
      (∑ j, (A.multiplicity i j : ℚ) * (output.weight j : ℚ)) =
        (A.degree i : ℚ) * (output.weight i : ℚ) := by
    exact_mod_cast valid.balance i
  rw [hbalance, sub_self]
  rfl

/-- The checked integral vector solves the normalized normal equations. -/
theorem normalMatrix_mulVec_natCast_eq_rhs
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    normalMatrix A *ᵥ (fun i ↦ (output.weight i : ℚ)) =
      normalizedRhs A := by
  rw [normalMatrix, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    residualMatrix_mulVec_natCast_eq_zero A output valid,
    Matrix.mulVec_zero, zero_add, leaderProjector_mulVec]
  funext i
  simp [normalizedRhs, valid.leader_weight]

/-- Rational strong connectivity extracted from the executable support
checker. -/
theorem rational_support_stronglyConnected
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    StronglyConnected
      (fun i j : Fin q ↦ 0 < (A.multiplicity i j : ℚ)) := by
  have hbool := strongConnectivityCheck_sound
    (IntegralAnchorInstance.support A)
    valid.support_strongly_connected
  simpa [IntegralAnchorInstance.support, Nat.cast_pos] using hbool

/-- The only residual-kernel vector with zero leader coordinate is zero. -/
theorem eq_zero_of_residual_eq_zero_of_leader_eq_zero
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output)
    (x : Fin q → ℚ)
    (hresidual : residualMatrix A *ᵥ x = 0)
    (hleader : x A.leader = 0) :
    x = 0 := by
  letI : Nonempty (Fin q) := ⟨A.leader⟩
  have hyPos : ∀ i : Fin q, 0 < (output.weight i : ℚ) := by
    intro i
    exact_mod_cast valid.weight_pos i
  have hyEig : ∀ i : Fin q,
      (∑ j, (A.multiplicity i j : ℚ) * (output.weight j : ℚ)) =
        (A.degree i : ℚ) * (output.weight i : ℚ) := by
    intro i
    exact_mod_cast valid.balance i
  have hxEig : ∀ i : Fin q,
      (∑ j, (A.multiplicity i j : ℚ) * x j) =
        (A.degree i : ℚ) * x i := by
    intro i
    have hi := congrFun hresidual i
    rw [residualMatrix_mulVec_apply] at hi
    simpa only [Pi.zero_apply, sub_eq_zero] using hi
  obtain ⟨c, hc⟩ := eigenvector_proportional_of_stronglyConnected
    (fun i j : Fin q ↦ (A.multiplicity i j : ℚ))
    (fun i : Fin q ↦ (A.degree i : ℚ))
    (fun i : Fin q ↦ (output.weight i : ℚ)) x
    (fun _i _j ↦ by positivity)
    (rational_support_stronglyConnected A output valid)
    hyPos hyEig hxEig
  have hcZero : c = 0 := by
    have h := hc A.leader
    simpa [hleader, valid.leader_weight] using h.symm
  funext i
  simp [hc i, hcZero]

/-- The normal matrix has trivial kernel. -/
theorem eq_zero_of_normalMatrix_mulVec_eq_zero
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output)
    (x : Fin q → ℚ)
    (hnormal : normalMatrix A *ᵥ x = 0) :
    x = 0 := by
  have henergy := dotProduct_normalMatrix_mulVec A x
  rw [hnormal, dotProduct_zero] at henergy
  let z := residualMatrix A *ᵥ x
  have hzNonneg : 0 ≤ z ⬝ᵥ z := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _hi ↦ mul_self_nonneg (z i)
  have hleaderNonneg : 0 ≤ x A.leader * x A.leader :=
    mul_self_nonneg _
  have hzZero : z ⬝ᵥ z = 0 := by
    dsimp only [z]
    nlinarith
  have hleaderSqZero : x A.leader * x A.leader = 0 := by
    dsimp only [z] at hzNonneg
    nlinarith
  have hresidual : residualMatrix A *ᵥ x = 0 := by
    exact dotProduct_self_eq_zero.mp hzZero
  have hleader : x A.leader = 0 := by
    exact mul_self_eq_zero.mp hleaderSqZero
  exact eq_zero_of_residual_eq_zero_of_leader_eq_zero
    A output valid x hresidual hleader

/-- Injectivity of the exact normalized system. -/
theorem normalMatrix_mulVec_injective
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    Function.Injective (normalMatrix A).mulVec := by
  intro x y hxy
  have hzero : normalMatrix A *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsub := eq_zero_of_normalMatrix_mulVec_eq_zero
    A output valid (x - y) hzero
  exact sub_eq_zero.mp hsub

/-- The determinant used by Cramer's rule is nonzero. -/
theorem normalMatrix_det_ne_zero
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    (normalMatrix A).det ≠ 0 := by
  have hunit : IsUnit (normalMatrix A) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (normalMatrix_mulVec_injective A output valid)
  exact ((Matrix.isUnit_iff_isUnit_det (normalMatrix A)).mp hunit).ne_zero

/-! ## Executable Cramer solution -/

/-- Normalized exact rational solution computed by Cramer's rule. -/
def rationalSolution (A : IntegralAnchorInstance q) : Fin q → ℚ :=
  (normalMatrix A).det⁻¹ •
    Matrix.cramer (normalMatrix A) (normalizedRhs A)

/-- Cramer's vector solves the normalized system whenever an accepted
positive integral anchor exists. -/
theorem normalMatrix_mulVec_rationalSolution_eq_rhs
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    normalMatrix A *ᵥ rationalSolution A = normalizedRhs A := by
  have hdet := normalMatrix_det_ne_zero A output valid
  unfold rationalSolution
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer]
  simp [hdet]

/-- Correctness of the generator: its exact rational result is the cast of
the accepted positive integral profile. -/
theorem rationalSolution_eq_natCast
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    rationalSolution A = fun i ↦ (output.weight i : ℚ) := by
  apply normalMatrix_mulVec_injective A output valid
  rw [normalMatrix_mulVec_rationalSolution_eq_rhs A output valid,
    normalMatrix_mulVec_natCast_eq_rhs A output valid]

theorem rationalSolution_leader
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    rationalSolution A A.leader = 1 := by
  rw [rationalSolution_eq_natCast A output valid]
  change (output.weight A.leader : ℚ) = 1
  exact_mod_cast valid.leader_weight

theorem rationalSolution_balance
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) (i : Fin q) :
    (∑ j, (A.multiplicity i j : ℚ) * rationalSolution A j) =
      (A.degree i : ℚ) * rationalSolution A i := by
  rw [rationalSolution_eq_natCast A output valid]
  change (∑ j, (A.multiplicity i j : ℚ) * (output.weight j : ℚ)) =
    (A.degree i : ℚ) * (output.weight i : ℚ)
  exact_mod_cast valid.balance i

theorem rationalSolution_pos
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) (i : Fin q) :
    0 < rationalSolution A i := by
  rw [rationalSolution_eq_natCast A output valid]
  change (0 : ℚ) < (output.weight i : ℚ)
  exact_mod_cast valid.weight_pos i

/-! ## Executable conversion back to natural weights -/

/-- Convert a rational vector only when every coordinate is a nonnegative
integer in reduced representation. -/
def rationalVectorToNat? (x : Fin q → ℚ) : Option (Fin q → Nat) :=
  if ∀ i, (x i).den = 1 ∧ 0 ≤ (x i).num then
    some (fun i ↦ (x i).num.toNat)
  else none

/-- Conversion is a left inverse of the coordinatewise Nat cast. -/
theorem rationalVectorToNat?_natCast (y : Fin q → Nat) :
    rationalVectorToNat? (fun i ↦ (y i : ℚ)) = some y := by
  simp [rationalVectorToNat?]

/-- Fully executable exact anchor solver: Cramer over `ℚ`, followed by the
checked integral conversion. -/
def solveNat? (A : IntegralAnchorInstance q) : Option (Fin q → Nat) :=
  rationalVectorToNat? (rationalSolution A)

/-- On every accepted anchor instance, the executable solver returns exactly
the checked integral vector. -/
theorem solveNat?_eq_some
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    solveNat? A = some output.weight := by
  unfold solveNat?
  rw [rationalSolution_eq_natCast A output valid]
  exact rationalVectorToNat?_natCast output.weight

/-- Package the generated vector in the data-only format consumed by the
existing exact anchor checker. -/
def solveOutput? (candidate : Nat) (A : IntegralAnchorInstance q) :
    Option (IntegralAnchorInstance.Output q candidate) :=
  (solveNat? A).map fun weight ↦ ⟨weight⟩

theorem solveOutput?_eq_some
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    solveOutput? candidate A = some output := by
  unfold solveOutput?
  rw [solveNat?_eq_some A output valid]
  rfl

end ExactAnchorSolver
end DirectedCounting
