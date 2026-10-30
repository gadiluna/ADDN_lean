import Counting.CausalSupport
import DirectedCountingFormalization.PaperHistory

/-! The full-information semantics and the quotient-node model describe exactly
the same history classes. This bridges protocol indistinguishability, causal
visibility, and the concrete fiber/accounting lemmas. -/

namespace Counting
open DirectedCounting
open scoped BigOperators

theorem count_incoming {V A : Type} [Fintype V] [DecidableEq A]
    (edge : V → V → Nat) (state : V → A) (x : V) (a : A) :
    (incoming edge state x).count a = ∑ y, if state y = a then edge y x else 0 := by
  classical
  unfold incoming
  have aux : ∀ (s : Finset V),
      (∑ y ∈ s, Multiset.replicate (edge y x) (state y)).count a =
        ∑ y ∈ s, if state y = a then edge y x else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert b s hb ih => simp [Finset.sum_insert, hb, ih, Multiset.count_replicate]
  simpa using aux Finset.univ

/-- Exact equivalence with the paper's recursive class-count definition. -/
theorem history_eq_iff_sameMultigraphHistory {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat) (x y : V) :
    history G leader t x = history G leader t y ↔
      sameMultigraphHistory G leader t x y := by
  classical
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
      change (_ = _) ↔ (_ ∧ _ ∧ _)
      constructor
      · intro heq
        have hp := congrArg Prod.fst heq
        have hd := congrArg (fun h : FullHistory (t + 1) => h.2.1) heq
        have hm := congrArg (fun h : FullHistory (t + 1) => h.2.2) heq
        refine ⟨(ih x y).mp hp, hd, ?_⟩
        intro z
        have hc := congrArg (Multiset.count (history G leader t z)) hm
        simp only [history, count_incoming] at hc
        simpa only [weightedIncomingFromClass, ← ih] using hc
      · rintro ⟨hp, hd, hm⟩
        apply Prod.ext ((ih x y).mpr hp)
        apply Prod.ext hd
        apply Multiset.ext.mpr
        intro a
        simp only [history, count_incoming]
        by_cases ha : ∃ z, history G leader t z = a
        · obtain ⟨z, rfl⟩ := ha
          simpa only [weightedIncomingFromClass, ← ih] using hm z
        · have hnone : ∀ z, history G leader t z ≠ a := by simpa using ha
          simp [hnone]

/-- Node equality implies equal decisions for every anonymous protocol. -/
theorem Protocol.same_class_same_status {State V : Type} [Fintype V]
    (P : Protocol State) (ell : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (t : Nat) (x y : V)
    (h : sameMultigraphHistory G leader t x y) :
    P.trace ell G leader t x = P.trace ell G leader t y :=
  P.same_history_same_status ell G G leader leader t x y
    ((history_eq_iff_sameMultigraphHistory G leader t x y).mpr h)

end Counting
