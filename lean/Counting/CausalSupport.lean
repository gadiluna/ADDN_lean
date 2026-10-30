import Counting.Protocol
import DirectedCountingFormalization.PairedHistory

/-!
# Causal visibility in full-information histories

This file supplies the semantic visibility/support equivalence and the delay
bound H4. It does not assume that a visible fiber is wholly in causal support:
one representative of that history in the support is sufficient.
-/

namespace Counting
open DirectedCounting
open scoped BigOperators

theorem mem_incoming {V A : Type} [Fintype V] (edge : V → V → Nat)
    (state : V → A) (x : V) (a : A) :
    a ∈ incoming edge state x ↔ ∃ y, 0 < edge y x ∧ state y = a := by
  classical
  unfold incoming
  have aux : ∀ (s : Finset V),
      a ∈ ∑ y ∈ s, Multiset.replicate (edge y x) (state y) ↔
        ∃ y ∈ s, 0 < edge y x ∧ state y = a := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert b s hb ih =>
        simp [Finset.sum_insert, hb, ih, Multiset.mem_replicate, eq_comm, Nat.pos_iff_ne_zero]
  simpa using aux Finset.univ

/-- A history at level `r` occurs in the backward closure of an observer's history. -/
def Sees {r : Nat} (h : FullHistory r) : (d : Nat) → FullHistory (r + d) → Prop
  | 0, v => h = v
  | d + 1, v => Sees h d v.1 ∨ ∃ z ∈ v.2.2, Sees h d z

theorem temporalReach_succ_iff {V : Type} (G : Nat → V → V → Prop)
    (r : Nat) (source x : V) (d : Nat) :
    TemporalReach G r source (d + 1) x ↔
      TemporalReach G r source d x ∨
        ∃ y, TemporalReach G r source d y ∧ G (r + d + 1) y x := by
  constructor
  · intro h
    cases h with
    | stay h => exact Or.inl h
    | send h edge => exact Or.inr ⟨_, h, edge⟩
  · rintro (h | ⟨y, h, hedge⟩)
    · exact TemporalReach.stay h
    · exact TemporalReach.send h hedge

/-- Visibility means intersection of the history fiber with causal support. -/
theorem sees_iff_causal_support {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (x : V) (h : FullHistory r) :
    Sees h d (history G leader (r + d) x) ↔
      ∃ y, h = history G leader r y ∧
        TemporalReach (fun t u v => 0 < G t u v) r y d x := by
  induction d generalizing x with
  | zero =>
      constructor
      · intro hh
        exact ⟨x, hh, TemporalReach.zero⟩
      · rintro ⟨y, hh, hr⟩
        cases hr
        exact hh
  | succ d ih =>
      change (Sees h d (history G leader (r + d) x) ∨
        ∃ z ∈ incoming (G (r + d + 1)) (history G leader (r + d)) x,
          Sees h d z) ↔ _
      constructor
      · rintro (hold | ⟨z, hz, hseen⟩)
        · obtain ⟨y, hy, hp⟩ := (ih x).mp hold
          exact ⟨y, hy, TemporalReach.stay hp⟩
        · obtain ⟨v, hedge, hv⟩ := (mem_incoming _ _ _ _).mp hz
          rw [← hv] at hseen
          obtain ⟨y, hy, hp⟩ := (ih v).mp hseen
          exact ⟨y, hy, TemporalReach.send hp hedge⟩
      · rintro ⟨y, hy, hp⟩
        rcases (temporalReach_succ_iff _ _ _ _ _).mp hp with hold | ⟨v, hpv, hedge⟩
        · exact Or.inl ((ih x).mpr ⟨y, hy, hold⟩)
        · exact Or.inr ⟨history G leader (r + d) v,
            (mem_incoming _ _ _ _).mpr ⟨v, hedge, rfl⟩,
            (ih v).mpr ⟨y, hy, hpv⟩⟩

/-- The flooding theorem needs connectivity only at communication rounds. -/
theorem temporalReach_after_card_sub_one {V : Type} [Fintype V]
    (G : Nat → V → V → Prop)
    (hsc : ∀ t, 0 < t → StronglyConnected (G t))
    (start : Nat) (source target : V) :
    TemporalReach G start source (Fintype.card V - 1) target := by
  classical
  letI : Nonempty V := ⟨source⟩
  let informed := temporalInformed G start source
  let edge := fun k => G (start + k + 1)
  have initial : (informed 0).Nonempty := by
    exact ⟨source, (mem_temporalInformed _ _ _ _ _).mpr TemporalReach.zero⟩
  have mono : ∀ k, informed k ⊆ informed (k + 1) := by
    intro k v hv
    exact (mem_temporalInformed _ _ _ _ _).mpr
      (TemporalReach.stay ((mem_temporalInformed _ _ _ _ _).mp hv))
  have deliver : ∀ k ⦃u v⦄, u ∈ informed k → edge k u v → v ∈ informed (k + 1) := by
    intro k u v hu huv
    exact (mem_temporalInformed _ _ _ _ _).mpr
      (TemporalReach.send ((mem_temporalInformed _ _ _ _ _).mp hu) huv)
  have full := directed_flooding edge informed
    (fun k => hsc (start + k + 1) (by omega)) initial mono deliver
  have ht : target ∈ informed (Nat.card V - 1) := by
    rw [full]
    exact Finset.mem_univ target
  simpa [informed, Nat.card_eq_fintype_card] using ht

/-- H4: at distance at least `n-1`, every earlier history is visible. -/
theorem exhaustive_after_delay {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool)
    (hsc : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (r d : Nat) (hd : Fintype.card V - 1 ≤ d) (source observer : V) :
    Sees (history G leader r source) d (history G leader (r + d) observer) := by
  apply (sees_iff_causal_support G leader r d observer _).mpr
  refine ⟨source, rfl, ?_⟩
  have h := temporalReach_after_card_sub_one (fun t u v => 0 < G t u v) hsc r source observer
  induction d, hd using Nat.le_induction with
  | base => exact h
  | succ d hd ih => exact TemporalReach.stay ih

end Counting
