import Counting.LowerSeveralPhases

/-! Structural bounds of the two middle phases. -/

namespace Counting.LowerSeveralPhases
open DirectedCounting
open scoped BigOperators

/-- The full per-round graph requirements in the several-leader theorem. -/
structure RoundValid {V : Type} [Fintype V] (edge : V → V → Nat) (ell : Nat) : Prop where
  connected : StronglyConnected (fun u v ↦ 0 < edge u v)
  loopless : ∀ u, edge u u = 0
  multiplicity : ∀ u v, edge u v ≤ ell
  degree : ∀ u, (∑ v, edge u v) ≤ ell ^ 2

/-- The generic two-center graph has degree at most ell squared when its
right side contains at most ell agents. -/
theorem twoCenter_degree_le_square {U W : Type} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] (z : U) (z' : W) (c : Nat)
    (choice : c = 1 ∨ c = Fintype.card U) (rightSize : Fintype.card W ≤ Fintype.card U)
    (u : U ⊕ W) : (∑v, TwoCenter.edge z z' c u v) ≤ Fintype.card U ^ 2 := by
  have hpos := TwoCenter.left_card_pos z
  have hsquare : Fintype.card U ≤ Fintype.card U ^ 2 := by nlinarith
  cases u with
  | inl u =>
      by_cases hu : u = z
      · subst u
        rw [TwoCenter.center_outdegree]
        have hc : c ≤ Fintype.card U := by rcases choice with rfl | rfl <;> omega
        nlinarith [Nat.mul_le_mul hc rightSize]
      · rw [TwoCenter.left_outdegree z z' c u hu]
        exact (Nat.div_le_self _ _).trans hsquare
  | inr w => simpa only [TwoCenter.right_outdegree] using hsquare

theorem twoCenter_valid {U W : Type} [Fintype U] [Fintype W]
    [DecidableEq U] [DecidableEq W] (z : U) (z' : W) (c : Nat)
    (choice : c = 1 ∨ c = Fintype.card U) (rightSize : Fintype.card W ≤ Fintype.card U) :
    RoundValid (TwoCenter.edge z z' c) (Fintype.card U) where
  connected := TwoCenter.stronglyConnected z z' c choice
  loopless := TwoCenter.loopless z z' c
  multiplicity := TwoCenter.multiplicity_le_leaders z z' c choice
  degree := twoCenter_degree_le_square z z' c choice rightSize

theorem relabel_valid {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W)
    (edge : W → W → Nat) (ell : Nat) (h : RoundValid edge ell) :
    RoundValid (relabel e edge) ell where
  connected := relabel_connected e edge h.connected
  loopless := fun u ↦ h.loopless (e u)
  multiplicity := fun u v ↦ h.multiplicity (e u) (e v)
  degree := fun u ↦ by rw [relabel_degree]; exact h.degree (e u)

theorem relay_valid {N : Type} [Fintype N] [DecidableEq N]
    (k g : Nat) (core : (Leaders k ⊕ N) → (Leaders k ⊕ N) → Nat) (center : N)
    (fanout : ∀ l, core (.inr center) (.inl l) = 1) (valid : RoundValid core (k + 2)) :
    RoundValid (LowerSeveralRelay.edge core center g) (k + 2) where
  connected := LowerSeveralRelay.stronglyConnected core center g (by simp [Leaders]) valid.connected
  loopless := LowerSeveralRelay.loopless core center g valid.loopless
  multiplicity := by
    intro u v
    simpa [Leaders] using LowerSeveralRelay.multiplicity_le core center g (by simp [Leaders])
      (by simpa [Leaders] using valid.multiplicity) u v
  degree := LowerSeveralRelay.outdegree_le core center g ((k + 2)^2) fanout valid.degree (by
    simp only [Leaders, Fintype.card_fin]
    nlinarith)

theorem star_valid (k : Nat) : RoundValid (star k) (k + 2) where
  connected := star_connected k
  loopless := fun u ↦ by cases u <;> rfl
  multiplicity := fun u v ↦ by cases u <;> cases v <;> simp [star]
  degree := by
    intro u
    cases u with
    | inl l =>
        rw [star_leader_degree]
        simpa using Nat.pow_le_pow_left (show 1 ≤ k + 2 by omega) 2
    | inr n => cases n; rw [star_nonleader_degree]; nlinarith

theorem firstSmall_valid (k g : Nat) : RoundValid (firstSmall k g) (k + 2) :=
  relay_valid k g _ () (firstSmall_fanout k) (star_valid k)

theorem firstLarge_valid (k g : Nat) (i : Leaders k) : RoundValid (firstLarge k g i) (k + 2) := by
  apply relay_valid k g _ (observer k) (firstLarge_fanout k i)
  simpa [firstLargeCore, Leaders] using twoCenter_valid i (observer k) (k + 2) (Or.inr (by simp [Leaders])) le_rfl

theorem secondSmall_valid (k g : Nat) (i : Leaders k) : RoundValid (secondSmall k g i) (k + 2) := by
  apply relay_valid k g _ () (secondSmall_fanout k i)
  simpa [secondSmallCore, Leaders] using twoCenter_valid i () 1 (Or.inl rfl) (by simp [Leaders])

theorem secondLarge_valid (k g : Nat) (i : Leaders k) : RoundValid (secondLarge k g i) (k + 2) := by
  apply relay_valid k g _ i (secondLarge_fanout k i)
  apply relabel_valid
  simpa [Leaders] using twoCenter_valid i (observer k) 1 (Or.inl rfl) le_rfl

end Counting.LowerSeveralPhases
