import Counting.Credit
import Counting.MinimumRatio

/-!
# Credit loss for finite history quotients

This combines the refinement and minimum-ratio lemmas into the paper's
credit-preservation conclusion. Every actual node, including hidden nodes,
is represented in `Node`. The hypotheses are the partition, visibility,
flow, and leader-count conditions of a single accepted prefix step.

CreditHistory and the executable refinement modules derive these hypotheses
from concrete histories and Steps 1--4. No correctness or population
identification conclusion is included among the premises.
-/

namespace Counting

/-- A nonempty finite family whose actual total does not exceed its candidate
total contains a node whose actual anonymity does not exceed its candidate. -/
theorem exists_actual_le_candidate {Node : Type*} (s : Finset Node)
    (actual candidate : Node → ℕ) (hne : s.Nonempty)
    (hsum : (∑ i ∈ s, actual i) ≤ ∑ i ∈ s, candidate i) :
    ∃ i ∈ s, actual i ≤ candidate i := by
  by_contra h
  push Not at h
  have hstrict := Finset.sum_lt_sum_of_nonempty hne h
  omega

/-- Credit loss, equality case: preserving credit makes the visible level
exhaustive and fixes every candidate anonymity to the actual anonymity. -/
theorem credit_preserved_identifies_population
    {Node Parent : Type*} [Fintype Node] [DecidableEq Node] [DecidableEq Parent]
    (parent : Node → Parent) (visible : Finset Node) (previous : Finset Parent)
    (actual candidate degree : Node → ℕ) (weight : Parent → Node → ℕ)
    (oldActual oldCandidate : Parent → ℕ) (leaders : Finset Node) (ell : ℕ)
    (hactualpos : ∀ i, 0 < actual i)
    (hcandidatepos : ∀ i ∈ visible, 0 < candidate i)
    (hmaps : ∀ i ∈ visible, parent i ∈ previous)
    (hchildren : ∀ u ∈ previous, (visible.filter (fun i => parent i = u)).Nonempty)
    (hpartition : ∀ u, ∑ i ∈ Finset.univ.filter (fun i => parent i = u), actual i = oldActual u)
    (hbackward : ∀ u ∈ previous,
      ∑ i ∈ visible.filter (fun i => parent i = u), candidate i = oldCandidate u)
    (actualFlow : ∀ u,
      (∑ i, if parent i = u then degree i * actual i else 0) =
      ∑ i, weight u i * actual i)
    (candidateFlow : ∀ u ∈ previous,
      (∑ i ∈ visible, if parent i = u then degree i * candidate i else 0) =
      ∑ i ∈ visible, weight u i * candidate i)
    (connected : ∀ i j,
      Relation.ReflTransGen (fun p q => 0 < weight (parent p) q) i j)
    (hactualLeaders : ∑ i ∈ leaders, actual i = ell)
    (hcandidateLeaders : ∑ i ∈ visible ∩ leaders, candidate i = ell)
    (hell : 0 < ell)
    (hpreserved : (∑ i ∈ visible, credit (actual i) (candidate i)) =
      ∑ u ∈ previous, credit (oldActual u) (oldCandidate u)) :
    visible = Finset.univ ∧ actual = candidate := by
  have hleadersne : (visible ∩ leaders).Nonempty := by
    by_contra h
    have he : visible ∩ leaders = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hcandidateLeaders
    omega
  have hleadersbound : (∑ i ∈ visible ∩ leaders, actual i) ≤
      ∑ i ∈ visible ∩ leaders, candidate i := by
    rw [hcandidateLeaders, ← hactualLeaders]
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  obtain ⟨leader, hleader, hleaderle⟩ := exists_actual_le_candidate
    (visible ∩ leaders) actual candidate hleadersne hleadersbound
  have hleadervis := (Finset.mem_inter.mp hleader).1
  have hvisiblene : visible.Nonempty := ⟨leader, hleadervis⟩
  obtain ⟨minNode, hminNode, hminimum⟩ := Finset.exists_min_image visible
    (fun i => (actual i : ℚ) / candidate i) hvisiblene
  let alpha : ℚ := (actual minNode : ℚ) / candidate minNode
  have hmin : ∀ i ∈ visible, alpha * (candidate i : ℚ) ≤ actual i := by
    intro i hi
    exact (le_div_iff₀ (by exact_mod_cast hcandidatepos i hi)).mp (hminimum i hi)
  have hminimumEq : (actual minNode : ℚ) = alpha * (candidate minNode : ℚ) := by
    dsimp [alpha]
    rw [div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_of_gt (hcandidatepos minNode hminNode))]
  have halpha : alpha ≤ 1 := by
    have hleaderRatio : (actual leader : ℚ) / candidate leader ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hcandidatepos leader hleadervis)).mpr
      exact_mod_cast hleaderle
    exact le_trans (hminimum leader hleadervis) hleaderRatio
  have parentClosed : ∀ i,
      parent i ∈ (visible.filter (fun j => (actual j : ℚ) = alpha * candidate j)).image parent →
      i ∈ visible.filter (fun j => (actual j : ℚ) = alpha * candidate j) := by
    intro i hi
    obtain ⟨j, hj, hparent⟩ := Finset.mem_image.mp hi
    obtain ⟨hjvisible, hjratio⟩ := Finset.mem_filter.mp hj
    have hjle : actual j ≤ candidate j := by
      have hle : (actual j : ℚ) ≤ candidate j := by
        calc
          (actual j : ℚ) = alpha * candidate j := hjratio
          _ ≤ 1 * (candidate j : ℚ) := mul_le_mul_of_nonneg_right halpha (Nat.cast_nonneg _)
          _ = candidate j := one_mul _
      exact_mod_cast hle
    have hrigid := credit_preservation_saturated_parent_unique parent visible previous actual candidate
      oldActual oldCandidate hactualpos hmaps hchildren hpartition hbackward hpreserved j hjvisible hjle
    have hij := hrigid.1 i hparent.symm
    simpa only [hij] using hj
  have hactualFlowQ : ∀ u,
      (∑ i, if parent i = u then (degree i : ℚ) * actual i else 0) =
      ∑ i, (weight u i : ℚ) * actual i := by
    intro u
    exact_mod_cast actualFlow u
  have hcandidateFlowQ : ∀ u ∈ visible.image parent,
      (∑ i ∈ visible, if parent i = u then (degree i : ℚ) * candidate i else 0) =
      ∑ i ∈ visible, (weight u i : ℚ) * candidate i := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact_mod_cast candidateFlow (parent i) (hmaps i hi)
  have hconnectedQ : ∀ i j,
      Relation.ReflTransGen (fun p q => (0 : ℚ) < weight (parent p) q) i j := by
    simpa only [Nat.cast_pos] using connected
  obtain ⟨hfull, hratio⟩ := MinimumRatio.minimum_ratio_closure parent visible
    (fun i => (actual i : ℚ)) (fun i => (candidate i : ℚ)) (fun i => (degree i : ℚ))
    (fun u i => (weight u i : ℚ)) alpha (fun i => by exact_mod_cast hactualpos i)
    (fun _ _ => Nat.cast_nonneg _) hmin hactualFlowQ hcandidateFlowQ parentClosed
    ⟨minNode, Finset.mem_filter.mpr ⟨hminNode, hminimumEq⟩⟩ hconnectedQ
  have hcandidateLeadersAll : ∑ i ∈ leaders, candidate i = ell := by
    simpa only [hfull, Finset.univ_inter] using hcandidateLeaders
  have hleaderActualQ : (∑ i ∈ leaders, (actual i : ℚ)) = ell := by
    exact_mod_cast hactualLeaders
  have hleaderCandidateQ : (∑ i ∈ leaders, (candidate i : ℚ)) = ell := by
    exact_mod_cast hcandidateLeadersAll
  have hscale : alpha * (ell : ℚ) = ell := by
    calc
      alpha * (ell : ℚ) = alpha * (∑ i ∈ leaders, (candidate i : ℚ)) := by rw [hleaderCandidateQ]
      _ = ∑ i ∈ leaders, (actual i : ℚ) := by simp only [Finset.mul_sum, hratio]
      _ = ell := hleaderActualQ
  have halphaOne : alpha = 1 := by
    apply mul_right_cancel₀ (show (ell : ℚ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hell)
    simpa only [one_mul] using hscale
  refine ⟨hfull, funext fun i => ?_⟩
  have heq := hratio i
  rw [halphaOne, one_mul] at heq
  exact_mod_cast heq

end Counting
