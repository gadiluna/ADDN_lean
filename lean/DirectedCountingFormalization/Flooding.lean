import DirectedCountingFormalization.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option warningAsError true

/-!
# Directed flooding in dynamic strongly connected networks

This module proves the exact dissemination fact used by the counting
proof.  The communication relation may change in every round.  It is enough
that each individual round is strongly connected: whenever the informed set
is proper, that round has an edge leaving it, so at least one new vertex is
informed.
-/

namespace DirectedCounting

/-- A nonempty set that is closed under a strongly connected relation is the
whole vertex set.  No finiteness assumption is needed for this fact. -/
theorem closed_eq_univ_of_stronglyConnected
    {V : Type*} {edge : V → V → Prop}
    (hsc : StronglyConnected edge) {S : Set V}
    (hne : S.Nonempty)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ S → edge u v → v ∈ S) :
    S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  obtain ⟨u, hu⟩ := hne
  exact mem_of_reachable_of_closed hclosed (hsc u v) hu

/-- One-step monotonicity of informed sets extends to every later round. -/
lemma informed_mono_trans
    {V : Type*} [Fintype V]
    (informed : ℕ → Finset V)
    (hmono : ∀ t, informed t ⊆ informed (t + 1))
    {s t : ℕ} (hst : s ≤ t) :
    informed s ⊆ informed t := by
  induction t, hst using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ t hst ih =>
      exact ih.trans (by simpa [Nat.add_comm] using hmono t)

/-- If the informed set is still proper, a strongly connected round informs
at least one new vertex. -/
lemma informed_card_strictly_grows
    {V : Type*} [Fintype V]
    (edge : ℕ → V → V → Prop)
    (informed : ℕ → Finset V)
    (hsc : ∀ t, StronglyConnected (edge t))
    (hmono : ∀ t, informed t ⊆ informed (t + 1))
    (hdeliver : ∀ t ⦃u v : V⦄, u ∈ informed t → edge t u v →
      v ∈ informed (t + 1))
    {t : ℕ} (hne : (informed t).Nonempty)
    (hproper : informed t ≠ Finset.univ) :
    (informed t).card < (informed (t + 1)).card := by
  have hmissing : ∃ v, v ∉ informed t := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨u, v, hu, hv, huv⟩ := exists_edge_leaving (hsc t)
    (⟨hne.choose, hne.choose_spec⟩ : ∃ x, x ∈ (informed t : Set V))
    (hmissing : ∃ x, x ∉ (informed t : Set V))
  have hvnext : v ∈ informed (t + 1) := hdeliver t hu huv
  have hne_sets : informed t ≠ informed (t + 1) := by
    intro heq
    exact hv (heq.symm ▸ hvnext)
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hmono t, hne_sets⟩)

/--
Directed dynamic flooding: starting from any nonempty informed set, all
vertices are informed after at most `Nat.card V - 1` rounds.

The edge relation is allowed to change arbitrarily between rounds.  The two
operational hypotheses say that information is retained and is transmitted
along every edge present in the current round.
-/
theorem directed_flooding
    {V : Type*} [Fintype V] [Nonempty V]
    (edge : ℕ → V → V → Prop)
    (informed : ℕ → Finset V)
    (hsc : ∀ t, StronglyConnected (edge t))
    (hinitial : (informed 0).Nonempty)
    (hmono : ∀ t, informed t ⊆ informed (t + 1))
    (hdeliver : ∀ t ⦃u v : V⦄, u ∈ informed t → edge t u v →
      v ∈ informed (t + 1)) :
    informed (Nat.card V - 1) = Finset.univ := by
  rw [Nat.card_eq_fintype_card]
  let last := Fintype.card V - 1
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  by_contra hlast
  have hmono_trans {s t : ℕ} (hst : s ≤ t) : informed s ⊆ informed t :=
    informed_mono_trans informed hmono hst
  have hproper : ∀ t, t ≤ last → informed t ≠ Finset.univ := by
    intro t ht heq
    have hsub : informed t ⊆ informed last := hmono_trans ht
    have hall : Finset.univ ⊆ informed last := by simpa [heq] using hsub
    exact hlast (Finset.Subset.antisymm (Finset.subset_univ _) hall)
  have hnonempty : ∀ t, (informed t).Nonempty := by
    intro t
    exact hinitial.mono (hmono_trans (Nat.zero_le t))
  have hgrowth : ∀ t, t ≤ last → (informed 0).card + t ≤ (informed t).card := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
        have ht_le : t ≤ last := Nat.le_trans (Nat.le_succ t) ht
        have hstrict : (informed t).card < (informed (t + 1)).card :=
          informed_card_strictly_grows edge informed hsc hmono hdeliver
            (hnonempty t) (hproper t ht_le)
        have ih' := ih ht_le
        omega
  have hlarge := hgrowth last (Nat.le_refl last)
  have hinitial_card : 1 ≤ (informed 0).card :=
    Finset.one_le_card.mpr hinitial
  have hfull_card : Fintype.card V ≤ (informed last).card := by
    dsimp [last] at hlarge ⊢
    omega
  have hupper : (informed last).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (informed last)
  have heqcard : (informed last).card = Fintype.card V :=
    Nat.le_antisymm hupper hfull_card
  exact hlast (Finset.eq_univ_of_card (informed last) heqcard)

end DirectedCounting
