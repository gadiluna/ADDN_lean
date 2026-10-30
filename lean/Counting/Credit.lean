import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Credit under refinement

The credit is `min (actual - 1) candidate`, exactly as in the paper.
This file proves the arithmetic part of Lemma `lem:credit-refinement-split`
for an arbitrary finite nonempty family of visible children. It does not
assume that visible children exhaust the parent's fiber.
-/

namespace Counting

def credit (actual candidate : ℕ) : ℕ := min (actual - 1) candidate

theorem credit_le_candidate (actual candidate : ℕ) :
    credit actual candidate ≤ candidate := min_le_right _ _

theorem credit_add_one_le_actual {actual candidate : ℕ} (h : 0 < actual) :
    credit actual candidate + 1 ≤ actual := by
  have := min_le_left (actual - 1) candidate
  unfold credit
  omega

/-- Every visible child reserves its own representative. -/
theorem sum_credit_add_card_le {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (hpos : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, credit (a i) (b i)) + s.card ≤ ∑ i ∈ s, a i := by
  calc
    (∑ i ∈ s, credit (a i) (b i)) + s.card =
        ∑ i ∈ s, (credit (a i) (b i) + 1) := by
          simp [Finset.sum_add_distrib]
    _ ≤ ∑ i ∈ s, a i := Finset.sum_le_sum fun i hi =>
      credit_add_one_le_actual (hpos i hi)

/-- Disjoint refinement and backward propagation cannot increase credit. -/
theorem credit_under_refinement {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (A B : ℕ) (hne : s.Nonempty) (hpos : ∀ i ∈ s, 0 < a i)
    (hactual : ∑ i ∈ s, a i ≤ A) (hcandidate : ∑ i ∈ s, b i = B) :
    ∑ i ∈ s, credit (a i) (b i) ≤ credit A B := by
  have hc := sum_credit_add_card_le s a b hpos
  have hn := Finset.card_pos.mpr hne
  have hb : (∑ i ∈ s, credit (a i) (b i)) ≤ B := by
    rw [← hcandidate]
    exact Finset.sum_le_sum fun i _ => credit_le_candidate (a i) (b i)
  change (∑ i ∈ s, credit (a i) (b i)) ≤ min (A - 1) B
  exact le_min (by omega) hb

/-- The equality case of credit under refinement: a saturated child forces
the entire visible family to be that child, with both anonymities preserved. -/
theorem credit_refinement_rigidity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℕ) (A B : ℕ)
    (hpos : ∀ i ∈ s, 0 < a i)
    (hactual : ∑ i ∈ s, a i ≤ A) (hcandidate : ∑ i ∈ s, b i = B)
    (heq : ∑ i ∈ s, credit (a i) (b i) = credit A B)
    (j : ι) (hj : j ∈ s) (hsaturated : a j ≤ b j) :
    s = {j} ∧ a j = A ∧ b j = B := by
  have hstrict : (∑ i ∈ s, credit (a i) (b i)) < B := by
    rw [← hcandidate]
    apply Finset.sum_lt_sum (fun i _ => credit_le_candidate (a i) (b i))
    refine ⟨j, hj, ?_⟩
    have := credit_add_one_le_actual (candidate := b j) (hpos j hj)
    omega
  have hparent : credit A B = A - 1 := by
    unfold credit at *
    omega
  have hbound := sum_credit_add_card_le s a b hpos
  have hcardpos := Finset.card_pos.mpr (show s.Nonempty from ⟨j, hj⟩)
  have hApos : 0 < A := by
    have := Finset.single_le_sum (f := a) (fun i _ => Nat.zero_le (a i)) hj
    have := hpos j hj
    omega
  have hcard : s.card = 1 := by omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hji : j = i := by simpa [hi] using hj
  have hsingleton : s = {j} := by simpa [hji] using hi
  have ha : a j = A := by
    simp only [hsingleton, Finset.sum_singleton, Finset.card_singleton] at hactual hbound heq
    omega
  have hb : b j = B := by simpa [hsingleton] using hcandidate
  exact ⟨hsingleton, ha, hb⟩

/-- Converting equality of anonymities into equality of finite agent fibers
requires only the independently supplied refinement inclusion. -/
theorem fiber_eq_of_refinement_card_eq {Agent : Type*} [DecidableEq Agent]
    (child parent : Finset Agent) (hrefines : child ⊆ parent)
    (hcard : child.card = parent.card) : child = parent :=
  Finset.eq_of_subset_of_card_le hrefines hcard.ge

/-- Summing a per-parent credit inequality gives the total-credit inequality. -/
theorem total_credit_mono {Parent : Type*} (parents : Finset Parent)
    (oldCredit newCredit : Parent → ℕ)
    (h : ∀ p ∈ parents, newCredit p ≤ oldCredit p) :
    ∑ p ∈ parents, newCredit p ≤ ∑ p ∈ parents, oldCredit p :=
  Finset.sum_le_sum h

/-- Total credit preservation forces preservation at each parent. -/
theorem total_credit_eq_forces_local_eq {Parent : Type*}
    (parents : Finset Parent) (oldCredit newCredit : Parent → ℕ)
    (h : ∀ p ∈ parents, newCredit p ≤ oldCredit p)
    (heq : ∑ p ∈ parents, newCredit p = ∑ p ∈ parents, oldCredit p) :
    ∀ p ∈ parents, newCredit p = oldCredit p := by
  intro p hp
  by_contra hne
  have hlt : newCredit p < oldCredit p := lt_of_le_of_ne (h p hp) hne
  have := Finset.sum_lt_sum h ⟨p, hp, hlt⟩
  omega

/-- For a whole refinement step, preservation of total credit and saturation
of one child force that child to be the parent's only actual child, including
children that were not visible. The exact partition equation is essential. -/
theorem credit_preservation_saturated_parent_unique
    {Node Parent : Type*} [Fintype Node] [DecidableEq Node] [DecidableEq Parent]
    (parent : Node → Parent) (visible : Finset Node) (previous : Finset Parent)
    (actual candidate : Node → ℕ) (oldActual oldCandidate : Parent → ℕ)
    (hpos : ∀ i, 0 < actual i)
    (hmaps : ∀ i ∈ visible, parent i ∈ previous)
    (hchildren : ∀ u ∈ previous, (visible.filter (fun i => parent i = u)).Nonempty)
    (hpartition : ∀ u, ∑ i ∈ Finset.univ.filter (fun i => parent i = u), actual i = oldActual u)
    (hbackward : ∀ u ∈ previous,
      ∑ i ∈ visible.filter (fun i => parent i = u), candidate i = oldCandidate u)
    (hpreserved : (∑ i ∈ visible, credit (actual i) (candidate i)) =
      ∑ u ∈ previous, credit (oldActual u) (oldCandidate u))
    (j : Node) (hj : j ∈ visible) (hsaturated : actual j ≤ candidate j) :
    (∀ i, parent i = parent j → i = j) ∧
      actual j = oldActual (parent j) ∧ candidate j = oldCandidate (parent j) := by
  let childCredit := fun u =>
    ∑ i ∈ visible.filter (fun i => parent i = u), credit (actual i) (candidate i)
  have hbound : ∀ u, (∑ i ∈ visible.filter (fun i => parent i = u), actual i) ≤ oldActual u := by
    intro u
    rw [← hpartition u]
    apply Finset.sum_le_sum_of_subset
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  have hmono : ∀ u ∈ previous, childCredit u ≤ credit (oldActual u) (oldCandidate u) := by
    intro u hu
    exact credit_under_refinement _ actual candidate _ _ (hchildren u hu)
      (fun i _ => hpos i) (hbound u) (hbackward u hu)
  have hsum : (∑ u ∈ previous, childCredit u) =
      ∑ u ∈ previous, credit (oldActual u) (oldCandidate u) := by
    rw [← hpreserved]
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hlocal := total_credit_eq_forces_local_eq previous
    (fun u => credit (oldActual u) (oldCandidate u)) childCredit hmono hsum
    (parent j) (hmaps j hj)
  obtain ⟨_, ha, hb⟩ := credit_refinement_rigidity
    (visible.filter (fun i => parent i = parent j)) actual candidate _ _
    (fun i _ => hpos i) (hbound (parent j)) (hbackward (parent j) (hmaps j hj))
    hlocal j (Finset.mem_filter.mpr ⟨hj, rfl⟩) hsaturated
  refine ⟨?_, ha, hb⟩
  intro i hiparent
  by_contra hij
  have hjall : j ∈ Finset.univ.filter (fun k => parent k = parent j) := by simp
  have hiall : i ∈ Finset.univ.filter (fun k => parent k = parent j) := by simp [hiparent]
  have hstrict := Finset.single_lt_sum hij hjall hiall (hpos i)
    (fun k _ _ => Nat.zero_le (actual k))
  rw [hpartition, ← ha] at hstrict
  exact (lt_irrefl _) hstrict

end Counting
