import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Minimum-ratio closure

The finite quotient formulation of `lem:minimum-ratio-closure-split`.
`Node` indexes every actual current-level fiber, including hidden fibers;
`visible` is the subset present in a vista. `parent` maps to the previous
level. Actual flow is over all nodes; candidate flow is over visible nodes.
The crucial closure premise says that a parent of a minimum-ratio node
has no actual child outside the minimum-ratio set. Disjoint partitions
turn equality of the unions of agent fibers in the paper into this premise.
-/

namespace Counting.MinimumRatio

variable {Node Parent K : Type*} [Fintype Node] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- An outgoing-closed nonempty set in a strongly connected relation is full. -/
theorem closed_nonempty_eq_univ {Node : Type*} [Fintype Node] [DecidableEq Node]
    (r : Node → Node → Prop) (s : Finset Node) (hne : s.Nonempty)
    (hclosed : ∀ i ∈ s, ∀ j, r i j → j ∈ s)
    (connected : ∀ i j, Relation.ReflTransGen r i j) : s = Finset.univ := by
  obtain ⟨i, hi⟩ := hne
  apply Finset.eq_univ_of_forall
  intro j
  have hp := connected i j
  induction hp with
  | refl => exact hi
  | tail _ edge ih => exact hclosed _ ih _ edge

/-- Under parent closure, actual and candidate flow force every outgoing
positive-weight edge of a minimum node to end at another minimum node. -/
theorem minimum_nodes_closed [DecidableEq Node] [DecidableEq Parent]
    (parent : Node → Parent) (visible : Finset Node)
    (actual candidate degree : Node → K) (weight : Parent → Node → K) (alpha : K)
    (hactualpos : ∀ i, 0 < actual i)
    (hweight : ∀ u i, 0 ≤ weight u i)
    (hmin : ∀ i ∈ visible, alpha * candidate i ≤ actual i)
    (actualFlow : ∀ u,
      (∑ i, if parent i = u then degree i * actual i else 0) =
      ∑ i, weight u i * actual i)
    (candidateFlow : ∀ u ∈ visible.image parent,
      (∑ i ∈ visible, if parent i = u then degree i * candidate i else 0) =
      ∑ i ∈ visible, weight u i * candidate i)
    (parentClosed : ∀ i,
      parent i ∈ (visible.filter (fun j => actual j = alpha * candidate j)).image parent →
      i ∈ visible.filter (fun j => actual j = alpha * candidate j)) :
    ∀ i ∈ visible.filter (fun j => actual j = alpha * candidate j),
      ∀ j, 0 < weight (parent i) j →
      j ∈ visible.filter (fun k => actual k = alpha * candidate k) := by
  classical
  intro i hi j hij
  let u := parent i
  have hu : u ∈ (visible.filter (fun k => actual k = alpha * candidate k)).image parent :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have childrenMin : ∀ k, parent k = u →
      k ∈ visible ∧ actual k = alpha * candidate k := by
    intro k hk
    exact Finset.mem_filter.mp (parentClosed k (hk ▸ hu))
  have hrestrict : (∑ k, if parent k = u then degree k * actual k else 0) =
      ∑ k ∈ visible, if parent k = u then degree k * actual k else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ visible)
    intro k _ hk
    have hp : parent k ≠ u := fun h => hk (childrenMin k h).1
    simp [hp]
  have hbalance : (∑ k, weight u k * actual k) =
      alpha * ∑ k ∈ visible, weight u k * candidate k := by
    calc
      (∑ k, weight u k * actual k) =
          ∑ k, if parent k = u then degree k * actual k else 0 := (actualFlow u).symm
      _ = ∑ k ∈ visible, if parent k = u then degree k * actual k else 0 := hrestrict
      _ = alpha * (∑ k ∈ visible, if parent k = u then degree k * candidate k else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hp : parent k = u
        · simp only [hp, ite_true, (childrenMin k hp).2]
          ring
        · simp [hp]
      _ = alpha * ∑ k ∈ visible, weight u k * candidate k := by
        rw [candidateFlow u (Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩)]
  let lower := fun k => if k ∈ visible then alpha * (weight u k * candidate k) else 0
  have hle : ∀ k ∈ Finset.univ, lower k ≤ weight u k * actual k := by
    intro k _
    dsimp [lower]
    by_cases hk : k ∈ visible
    · simp only [hk, ite_true]
      calc
        alpha * (weight u k * candidate k) = weight u k * (alpha * candidate k) := by ring
        _ ≤ weight u k * actual k := mul_le_mul_of_nonneg_left (hmin k hk) (hweight u k)
    · simp only [hk, ite_false]
      exact mul_nonneg (hweight u k) (le_of_lt (hactualpos k))
  have hsum : (∑ k, lower k) = ∑ k, weight u k * actual k := by
    rw [hbalance, Finset.mul_sum]
    simp [lower]
  have hterm : lower j = weight u j * actual j := by
    by_contra hne
    have hstrict := Finset.sum_lt_sum hle
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hle j (Finset.mem_univ j)) hne⟩
    rw [hsum] at hstrict
    exact (lt_irrefl _) hstrict
  have hjvisible : j ∈ visible := by
    by_contra hj
    have hpositive := mul_pos hij (hactualpos j)
    simp only [lower, hj, ite_false] at hterm
    change 0 = weight (parent i) j * actual j at hterm
    linarith
  apply Finset.mem_filter.mpr
  refine ⟨hjvisible, ?_⟩
  simp only [lower, hjvisible, ite_true] at hterm
  apply (mul_left_cancel₀ (ne_of_gt hij))
  change weight u j * actual j = weight u j * (alpha * candidate j)
  calc
    weight u j * actual j = alpha * (weight u j * candidate j) := hterm.symm
    _ = weight u j * (alpha * candidate j) := by ring

/-- Minimum-ratio closure: all actual nodes are visible and have the same
ratio. This conclusion includes hidden nodes, rather than assuming that
the visible level is exhaustive. -/
theorem minimum_ratio_closure [DecidableEq Node] [DecidableEq Parent]
    (parent : Node → Parent) (visible : Finset Node)
    (actual candidate degree : Node → K) (weight : Parent → Node → K) (alpha : K)
    (hactualpos : ∀ i, 0 < actual i)
    (hweight : ∀ u i, 0 ≤ weight u i)
    (hmin : ∀ i ∈ visible, alpha * candidate i ≤ actual i)
    (actualFlow : ∀ u,
      (∑ i, if parent i = u then degree i * actual i else 0) =
      ∑ i, weight u i * actual i)
    (candidateFlow : ∀ u ∈ visible.image parent,
      (∑ i ∈ visible, if parent i = u then degree i * candidate i else 0) =
      ∑ i ∈ visible, weight u i * candidate i)
    (parentClosed : ∀ i,
      parent i ∈ (visible.filter (fun j => actual j = alpha * candidate j)).image parent →
      i ∈ visible.filter (fun j => actual j = alpha * candidate j))
    (hne : (visible.filter (fun j => actual j = alpha * candidate j)).Nonempty)
    (connected : ∀ i j,
      Relation.ReflTransGen (fun p q => 0 < weight (parent p) q) i j) :
    visible = Finset.univ ∧ ∀ i, actual i = alpha * candidate i := by
  have hc := minimum_nodes_closed parent visible actual candidate degree weight alpha
    hactualpos hweight hmin actualFlow candidateFlow parentClosed
  have hfull := closed_nonempty_eq_univ (fun p q => 0 < weight (parent p) q)
    (visible.filter (fun j => actual j = alpha * candidate j)) hne hc connected
  have hall : ∀ i, i ∈ visible ∧ actual i = alpha * candidate i := by
    intro i
    exact Finset.mem_filter.mp (hfull ▸ Finset.mem_univ i)
  exact ⟨Finset.eq_univ_of_forall (fun i => (hall i).1), fun i => (hall i).2⟩

end Counting.MinimumRatio
