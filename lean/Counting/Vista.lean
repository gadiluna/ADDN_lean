import Counting.Network

/-! Semantic vista levels as the backward closure of the observer's history.
The compact executable DAG is a separate representation requiring refinement.
-/

namespace Counting
open DirectedCounting PaperHistory

noncomputable def causalSupport {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (observer : V) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun source => TemporalReach (fun t u v => 0 < G t u v) r source d observer)

noncomputable def visibleNodes {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer : V) : Finset (Node G leader r) := by
  classical
  exact (causalSupport G r d observer).image (classOf G leader r)

/-- A semantic history-tree node is visible iff its fiber meets causal support. -/
theorem visible_iff_fiber_meets_support {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer : V) (node : Node G leader r) :
    node ∈ visibleNodes G leader r d observer ↔
      ∃ v ∈ fiber G leader r node, v ∈ causalSupport G r d observer := by
  classical
  simp only [visibleNodes, Finset.mem_image, mem_fiber]
  aesop

/-- Observable history occurrence agrees exactly with quotient-node visibility. -/
theorem visible_iff_sees {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer source : V) :
    classOf G leader r source ∈ visibleNodes G leader r d observer ↔
      Sees (history G leader r source) d (history G leader (r + d) observer) := by
  classical
  rw [sees_iff_causal_support]
  simp only [visibleNodes, Finset.mem_image, causalSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, classOf_eq_iff]
  constructor
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, ((history_eq_iff_sameMultigraphHistory G leader r v source).mpr hs).symm, hv⟩
  · rintro ⟨v, hs, hv⟩
    exact ⟨v, hv, (history_eq_iff_sameMultigraphHistory G leader r v source).mp hs.symm⟩

/-- H4 stated for the actual quotient history-tree nodes. -/
theorem vista_level_exhaustive {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool)
    (hsc : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (r d : Nat) (hd : Fintype.card V - 1 ≤ d) (observer : V) :
    visibleNodes G leader r d observer = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro node
  have hs := exhaustive_after_delay G leader hsc r d hd node.out observer
  have hm := (visible_iff_sees G leader r d observer node.out).mpr hs
  simpa using hm

/-- H1 for the particular level of an actual observer vista. -/
theorem vista_mass_le {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat) (observer : V) :
    (∑ node ∈ visibleNodes G leader r d observer, anonymity G leader r node) ≤
      Fintype.card V :=
  visible_mass_le G leader r _

end Counting
