import Counting.Vista

/-! Backward expansion of actual causal support and the tail-exposure bound. -/

namespace Counting
open DirectedCounting PaperHistory

theorem temporalReach_first_iff {V : Type} (G : Nat → V → V → Prop)
    (r : Nat) (source target : V) (d : Nat) :
    TemporalReach G r source (d + 1) target ↔
      TemporalReach G (r + 1) source d target ∨
        ∃ next, G (r + 1) source next ∧
          TemporalReach G (r + 1) next d target := by
  induction d generalizing target with
  | zero =>
      constructor
      · intro h
        cases h with
        | stay h => cases h; exact Or.inl TemporalReach.zero
        | send h e => cases h; exact Or.inr ⟨_, e, TemporalReach.zero⟩
      · rintro (h | ⟨next, e, h⟩)
        · cases h; exact TemporalReach.stay TemporalReach.zero
        · cases h; exact TemporalReach.send TemporalReach.zero e
  | succ d ih =>
      rw [temporalReach_succ_iff]
      simp only [ih, temporalReach_succ_iff]
      have heq : r + (d + 1) + 1 = r + 1 + d + 1 := by omega
      rw [heq]
      aesop

@[simp] theorem causalSupport_zero {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r : Nat) (x : V) :
    causalSupport G r 0 x = {x} := by
  classical
  ext y
  simp only [causalSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact TemporalReach.zero

theorem mem_causalSupport_succ {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (x y : V) :
    y ∈ causalSupport G r (d + 1) x ↔
      y ∈ causalSupport G (r + 1) d x ∨
        ∃ z ∈ causalSupport G (r + 1) d x, 0 < G (r + 1) y z := by
  classical
  simp only [causalSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    temporalReach_first_iff]
  aesop

theorem causalSupport_backward_subset {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (x : V) :
    causalSupport G (r + 1) d x ⊆ causalSupport G r (d + 1) x := by
  intro y hy
  exact (mem_causalSupport_succ G r d x y).mpr (Or.inl hy)

theorem observer_mem_causalSupport {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (x : V) :
    x ∈ causalSupport G r d x := by
  classical
  induction d generalizing r with
  | zero => simp
  | succ d ih => exact causalSupport_backward_subset G r d x (ih (r + 1))

/-- If a causal support is proper, the preceding support is strictly larger. -/
theorem causalSupport_strict_expansion {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (x : V)
    (hsc : StronglyConnected (fun u v => 0 < G (r + 1) u v))
    (hproper : causalSupport G (r + 1) d x ≠ Finset.univ) :
    (causalSupport G (r + 1) d x).card < (causalSupport G r (d + 1) x).card := by
  classical
  have hmissing : ∃ y, y ∉ causalSupport G (r + 1) d x := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨u, v, hu, hv, huv⟩ := exists_edge_leaving hsc
    (Q := {y | y ∉ causalSupport G (r + 1) d x}) hmissing
    ⟨x, by simpa using observer_mem_causalSupport G (r + 1) d x⟩
  have hv' : v ∈ causalSupport G (r + 1) d x := by simpa using hv
  have hu' : u ∈ causalSupport G r (d + 1) x :=
    (mem_causalSupport_succ G r d x u).mpr (Or.inr ⟨v, hv', huv⟩)
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨causalSupport_backward_subset G r d x, ?_⟩
  intro heq
  exact hu (heq.symm ▸ hu')

theorem causalSupport_card_lower_bound {V : Type} [Fintype V]
    (G : Nat → V → V → Nat)
    (hsc : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (r d : Nat) (x : V) :
    min (Fintype.card V) (d + 1) ≤ (causalSupport G r d x).card := by
  classical
  induction d generalizing r with
  | zero => simp
  | succ d ih =>
      have hi := ih (r + 1)
      by_cases hfull : causalSupport G (r + 1) d x = Finset.univ
      · have hn := Finset.card_le_card (causalSupport_backward_subset G r d x)
        rw [hfull, Finset.card_univ] at hn
        exact (min_le_left _ _).trans hn
      · have hg := causalSupport_strict_expansion G r d x
          (hsc (r + 1) (by omega)) hfull
        omega

/-- Tail exposure for actual visible fibers, including depth zero and n=1. -/
theorem tail_exposure {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool)
    (hsc : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (r d : Nat) (x : V) :
    min (Fintype.card V) (d + 1) ≤
      ∑ node ∈ visibleNodes G leader r d x, anonymity G leader r node := by
  classical
  rw [sum_anonymity_eq_card_filter]
  apply (causalSupport_card_lower_bound G hsc r d x).trans
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩

end Counting
