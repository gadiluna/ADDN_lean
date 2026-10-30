import Mathlib
import DirectedCountingFormalization.CertificateArithmetic
import DirectedCountingFormalization.Connectivity

/-!
# Uniqueness of a balanced eigenvector on strongly connected support

This file proves the full eigenspace statement used by the counting
certificate.  The proof is an elementary maximum principle: normalize an
arbitrary eigenvector coordinatewise by the fixed positive eigenvector, take
a maximal ratio, and use a positive edge leaving the maximal-ratio set.

No sign assumption is made on the arbitrary eigenvector `x`.
-/

open scoped BigOperators

namespace DirectedCounting

section RationalMatrix

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/--
If a rational matrix has strongly connected positive support and has a
strictly positive right eigenvector for a coordinatewise diagonal action,
then every other right eigenvector for that same action is proportional to
it.  The second eigenvector is allowed to have arbitrary signs.
-/
theorem eigenvector_proportional_of_stronglyConnected
    (M : ι → ι → ℚ) (d y x : ι → ℚ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hsc : StronglyConnected (fun i j ↦ 0 < M i j))
    (hy : ∀ i, 0 < y i)
    (hyEig : ∀ i, ∑ j, M i j * y j = d i * y i)
    (hxEig : ∀ i, ∑ j, M i j * x j = d i * x i) :
    ∃ c : ℚ, ∀ i, x i = c * y i := by
  classical
  let ratio : ι → ℚ := fun i ↦ x i / y i
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ ratio Finset.univ_nonempty
  let m : ℚ := ratio k
  have hratio_le : ∀ i, ratio i ≤ m := by
    intro i
    exact hk i (Finset.mem_univ i)
  have hy_ne : ∀ i, y i ≠ 0 := fun i ↦ (hy i).ne'
  have hrecover : ∀ i, y i * ratio i = x i := by
    intro i
    dsimp only [ratio]
    exact mul_div_cancel₀ (x i) (hy_ne i)
  have hratio_eq : ∀ i, ratio i = m := by
    by_contra hnot
    simp only [not_forall] at hnot
    obtain ⟨outside, houtside⟩ := hnot
    let Q : Set ι := {i | ratio i = m}
    have hQ : ∃ i, i ∈ Q := by
      refine ⟨k, ?_⟩
      change ratio k = m
      rfl
    have hproper : ∃ i, i ∉ Q := by
      refine ⟨outside, ?_⟩
      change ratio outside ≠ m
      exact houtside
    obtain ⟨i, j, hiQ, hjQ, hij⟩ :=
      exists_edge_leaving hsc hQ hproper
    change ratio i = m at hiQ
    change ratio j ≠ m at hjQ
    have hjlt : ratio j < m :=
      lt_of_le_of_ne (hratio_le j) hjQ
    have hsum :
        (∑ t, M i t * y t * (m - ratio t)) = 0 := by
      calc
        (∑ t, M i t * y t * (m - ratio t)) =
            ∑ t, (m * (M i t * y t) - M i t * x t) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [← hrecover t]
              ring
        _ = m * (∑ t, M i t * y t) - ∑ t, M i t * x t := by
              rw [Finset.mul_sum, Finset.sum_sub_distrib]
        _ = m * (d i * y i) - d i * x i := by
              rw [hyEig i, hxEig i]
        _ = 0 := by
              rw [← hrecover i, hiQ]
              ring
    have hterm_nonneg :
        ∀ t ∈ Finset.univ, 0 ≤ M i t * y t * (m - ratio t) := by
      intro t _
      exact mul_nonneg
        (mul_nonneg (hM i t) (le_of_lt (hy t)))
        (sub_nonneg.mpr (hratio_le t))
    have hjzero : M i j * y j * (m - ratio j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum
        j (Finset.mem_univ j)
    have hjpos : 0 < M i j * y j * (m - ratio j) :=
      mul_pos (mul_pos hij (hy j)) (sub_pos.mpr hjlt)
    exact hjpos.ne' hjzero
  refine ⟨m, ?_⟩
  intro i
  calc
    x i = y i * ratio i := (hrecover i).symm
    _ = y i * m := by rw [hratio_eq i]
    _ = m * y i := by ring

/--
Leader normalization fixes the proportionality constant, so two eigenvectors
with the same normalized leader coordinate are equal.
-/
theorem eigenvector_eq_of_leader_normalized
    (M : ι → ι → ℚ) (d y x : ι → ℚ) (leader : ι)
    (hM : ∀ i j, 0 ≤ M i j)
    (hsc : StronglyConnected (fun i j ↦ 0 < M i j))
    (hy : ∀ i, 0 < y i)
    (hyEig : ∀ i, ∑ j, M i j * y j = d i * y i)
    (hxEig : ∀ i, ∑ j, M i j * x j = d i * x i)
    (hyLeader : y leader = 1) (hxLeader : x leader = 1) :
    x = y := by
  obtain ⟨c, hc⟩ :=
    eigenvector_proportional_of_stronglyConnected M d y x hM hsc hy hyEig hxEig
  have hc_one : c = 1 := by
    have hleader := hc leader
    rw [hyLeader, hxLeader, mul_one] at hleader
    exact hleader.symm
  funext i
  rw [hc i, hc_one, one_mul]

/--
Nat-valued wrapper matching the paper's test-window data.  The balanced
system is checked over `ℕ`; an arbitrary candidate solution `x` is solved
over `ℚ`.  Casting the checked Nat solution to the rationals and fixing its
leader coordinate makes that rational solution unique.
-/
theorem rational_eigenvector_eq_natCast_of_leader_normalized
    (M : ι → ι → ℕ) (d y : ι → ℕ) (x : ι → ℚ) (leader : ι)
    (hsc : StronglyConnected (fun i j ↦ 0 < M i j))
    (hy : ∀ i, 0 < y i)
    (hyEig : ∀ i, ∑ j, M i j * y j = d i * y i)
    (hxEig : ∀ i,
      ∑ j, (M i j : ℚ) * x j = (d i : ℚ) * x i)
    (hyLeader : y leader = 1) (hxLeader : x leader = 1) :
    x = fun i ↦ (y i : ℚ) := by
  have hsc_rat :
      StronglyConnected (fun i j ↦ 0 < (M i j : ℚ)) := by
    simpa only [Nat.cast_pos] using hsc
  have hy_rat : ∀ i, 0 < (y i : ℚ) := by
    intro i
    exact_mod_cast hy i
  have hyEig_rat : ∀ i,
      ∑ j, (M i j : ℚ) * (y j : ℚ) =
        (d i : ℚ) * (y i : ℚ) := by
    intro i
    exact_mod_cast hyEig i
  have hyLeader_rat : (y leader : ℚ) = 1 := by
    exact_mod_cast hyLeader
  exact eigenvector_eq_of_leader_normalized
    (fun i j ↦ (M i j : ℚ)) (fun i ↦ (d i : ℚ))
    (fun i ↦ (y i : ℚ)) x leader
    (fun _ _ ↦ by positivity)
    hsc_rat hy_rat hyEig_rat hxEig hyLeader_rat hxLeader

/-- The recursive sum used by the arithmetic kernel is the ordinary sum over
`Fin q`.  This lemma is kept local to the wrapper layer. -/
private theorem sumN_eq_sum_range (q : ℕ) (f : ℕ → ℕ) :
    sumN q f = ∑ i ∈ Finset.range q, f i := by
  induction q with
  | zero => simp
  | succ q ih => simp [ih, Finset.sum_range_succ]

/--
Direct adapter from the official `BalancedRowSystem` representation to the
rational uniqueness theorem.  Thus the Nat-valued matrix, degrees, and
candidate vector checked by a test window have exactly one rational solution
whose leader coordinate is one.
-/
theorem rational_solution_eq_natCast_of_balancedRowSystem
    {q : ℕ} (M : ℕ → ℕ → ℕ) (d y : ℕ → ℕ)
    (x : Fin q → ℚ) (leader : Fin q)
    (hy : ∀ i, i < q → 0 < y i)
    (hBalance : BalancedRowSystem q M d y)
    (hsc : StronglyConnected
      (fun i j : Fin q ↦ 0 < M i.1 j.1))
    (hxEig : ∀ i : Fin q,
      ∑ j : Fin q, (M i.1 j.1 : ℚ) * x j =
        (d i.1 : ℚ) * x i)
    (hyLeader : y leader.1 = 1) (hxLeader : x leader = 1) :
    x = fun i ↦ (y i.1 : ℚ) := by
  letI : Nonempty (Fin q) := ⟨leader⟩
  have hyFin : ∀ i : Fin q, 0 < y i.1 := by
    intro i
    exact hy i.1 i.2
  have hyEigFin : ∀ i : Fin q,
      ∑ j : Fin q, M i.1 j.1 * y j.1 = d i.1 * y i.1 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ M i.1 j * y j)]
    simpa only [rowSum, sumN_eq_sum_range] using hBalance i.1 i.2
  exact rational_eigenvector_eq_natCast_of_leader_normalized
    (fun i j : Fin q ↦ M i.1 j.1) (fun i : Fin q ↦ d i.1)
    (fun i : Fin q ↦ y i.1) x leader hsc hyFin hyEigFin hxEig
    hyLeader hxLeader

end RationalMatrix

end DirectedCounting
