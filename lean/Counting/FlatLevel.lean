import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Uniqueness for flat-level flow equations

This is the linear-algebra argument of Appendix `app:flat-anonymities`.
The hypothesis `connected` concerns the directed support of the quotient
matrix. A separate history-tree theorem must supply that hypothesis from
the concrete round graph, together with exhaustiveness and flatness.
-/

namespace Counting.FlatLevel

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The row form of the paper's flow equations, before subtracting the diagonal. -/
def Flow (weight : ι → ι → K) (degree vector : ι → K) : Prop :=
  ∀ i, ∑ j, weight i j * vector j = degree i * vector i

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A linear combination of flow solutions is again a flow solution. -/
theorem flow_sub (weight : ι → ι → K) (degree x z : ι → K) (c : K)
    (hx : Flow weight degree x) (hz : Flow weight degree z) :
    Flow weight degree (fun i => c * x i - z i) := by
  intro i
  calc
    ∑ j, weight i j * (c * x j - z j) =
        c * (∑ j, weight i j * x j) - ∑ j, weight i j * z j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = degree i * (c * x i - z i) := by
      rw [hx i, hz i]
      ring

/-- A zero coordinate in a nonnegative solution propagates along positive edges. -/
theorem zero_of_positive_edge (weight : ι → ι → K) (degree vector : ι → K)
    (hweight : ∀ i j, 0 ≤ weight i j) (hvector : ∀ i, 0 ≤ vector i)
    (hflow : Flow weight degree vector) {i j : ι}
    (hi : vector i = 0) (hij : 0 < weight i j) : vector j = 0 := by
  have hsum : ∑ k, weight i k * vector k = 0 := by
    rw [hflow i, hi, mul_zero]
  have hterm : weight i j * vector j = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hweight i k) (hvector k))).mp hsum j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hij)

theorem zero_of_reachable (weight : ι → ι → K) (degree vector : ι → K)
    (hweight : ∀ i j, 0 ≤ weight i j) (hvector : ∀ i, 0 ≤ vector i)
    (hflow : Flow weight degree vector) {i j : ι}
    (hi : vector i = 0)
    (hpath : Relation.ReflTransGen (fun p q => 0 < weight p q) i j) :
    vector j = 0 := by
  induction hpath with
  | refl => exact hi
  | tail _ hedge ih => exact zero_of_positive_edge weight degree vector hweight hvector hflow ih hedge

/-- A positive flow solution spans the solution space when the support is
strongly connected. This applies over both the rationals and the reals. -/
theorem flow_solution_proportional [Nonempty ι]
    (weight : ι → ι → K) (degree x z : ι → K)
    (hweight : ∀ i j, 0 ≤ weight i j) (hxpos : ∀ i, 0 < x i)
    (connected : ∀ i j, Relation.ReflTransGen (fun p q => 0 < weight p q) i j)
    (hx : Flow weight degree x) (hz : Flow weight degree z) :
    ∃ c : K, ∀ i, z i = c * x i := by
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => z j / x j)
    Finset.univ_nonempty
  let c := z i / x i
  let vector := fun j => c * x j - z j
  have hvector : ∀ j, 0 ≤ vector j := by
    intro j
    have := (div_le_iff₀ (hxpos j)).mp (hmax j (Finset.mem_univ j))
    dsimp [vector, c]
    linarith
  have hzero : vector i = 0 := by
    dsimp [vector, c]
    rw [div_mul_cancel₀ _ (ne_of_gt (hxpos i)), sub_self]
  have hflow : Flow weight degree vector := flow_sub weight degree x z c hx hz
  refine ⟨c, fun j => ?_⟩
  have hzeroj := zero_of_reachable weight degree vector hweight hvector hflow hzero
    (connected i j)
  dsimp [vector] at hzeroj
  linarith

/-- A nonzero known leader total fixes the proportionality factor uniquely. -/
theorem flow_solution_unique_of_leader_total [Nonempty ι]
    (weight : ι → ι → K) (degree x z : ι → K) (leaders : Finset ι) (ell : K)
    (hweight : ∀ i j, 0 ≤ weight i j) (hxpos : ∀ i, 0 < x i)
    (connected : ∀ i j, Relation.ReflTransGen (fun p q => 0 < weight p q) i j)
    (hx : Flow weight degree x) (hz : Flow weight degree z)
    (hxleaders : ∑ i ∈ leaders, x i = ell)
    (hzleaders : ∑ i ∈ leaders, z i = ell) (hell : ell ≠ 0) : z = x := by
  obtain ⟨c, hc⟩ := flow_solution_proportional weight degree x z hweight hxpos connected hx hz
  have htotal : c * ell = ell := by
    calc
      c * ell = c * (∑ i ∈ leaders, x i) := by rw [hxleaders]
      _ = ∑ i ∈ leaders, z i := by simp only [Finset.mul_sum, hc]
      _ = ell := hzleaders
  have hc1 : c = 1 := by
    apply (mul_right_cancel₀ hell)
    simpa using htotal
  funext i
  simpa [hc1] using hc i

end Counting.FlatLevel
