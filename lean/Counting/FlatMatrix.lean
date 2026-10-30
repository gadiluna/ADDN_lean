import Counting.FlatLevel

/-! The general nonnegative-off-diagonal kernel argument used in the appendix. -/

namespace Counting.FlatMatrix
open scoped Matrix BigOperators

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A strongly connected positive support and a positive kernel vector force
every kernel vector to be proportional. Diagonal entries may have either sign. -/
theorem kernel_proportional (M : Matrix ι ι K) (x z : ι → K)
    (offDiagonal : ∀ i j, i ≠ j → 0 ≤ M i j)
    (positive : ∀ i, 0 < x i)
    (connected : ∀ i j, Relation.ReflTransGen (fun p q => 0 < M p q) i j)
    (hx : M *ᵥ x = 0) (hz : M *ᵥ z = 0) :
    ∃ c : K, ∀ i, z i = c * x i := by
  let shift : ι → K := fun i => max 0 (-M i i)
  let weight : ι → ι → K := fun i j => M i j + if i = j then shift i else 0
  have nonnegative : ∀ i j, 0 ≤ weight i j := by
    intro i j
    by_cases heq : i = j
    · subst j
      dsimp [weight, shift]
      simp only [if_true]
      have := le_max_right (0 : K) (-M i i)
      linarith
    · simpa [weight, heq] using offDiagonal i j heq
  have flow : ∀ v : ι → K, M *ᵥ v = 0 → FlatLevel.Flow weight shift v := by
    intro v hv i
    have row : (∑ j, M i j * v j) = 0 := congrFun hv i
    calc
      (∑ j, weight i j * v j) = (∑ j, M i j * v j) + shift i * v i := by
        simp [weight, add_mul, ite_mul, Finset.sum_add_distrib]
      _ = shift i * v i := by rw [row, zero_add]
  have support : ∀ i j, Relation.ReflTransGen (fun p q => 0 < weight p q) i j := by
    intro i j
    have path := connected i j
    induction path with
    | refl => exact .refl
    | @tail p q _ hpq ih =>
      apply ih.tail
      dsimp [weight]
      have hs : 0 ≤ (if p = q then shift p else 0) := by
        split_ifs
        · exact le_max_left _ _
        · exact le_refl _
      linarith
  exact FlatLevel.flow_solution_proportional weight shift x z
    nonnegative positive support (flow x hx) (flow z hz)

end Counting.FlatMatrix
