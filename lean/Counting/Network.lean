import Counting.HistoryBridge

/-! Admissible networks and universal correctness. Round zero carries inputs;
connectivity is required only at rounds 1,2,... . -/

namespace Counting
open DirectedCounting

def CutConnected {V : Type} [Fintype V] (edge : V → V → Nat) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    ∃ u ∈ S, ∃ v, v ∉ S ∧ 0 < edge u v

theorem cutConnected_iff {V : Type} [Fintype V] (edge : V → V → Nat) :
    CutConnected edge ↔ StronglyConnected (fun u v => 0 < edge u v) := by
  classical
  constructor
  · intro hc x y
    let S := Finset.univ.filter (fun z => Relation.ReflTransGen (fun u v => 0 < edge u v) x z)
    have hmem (z : V) : z ∈ S ↔ Relation.ReflTransGen (fun u v => 0 < edge u v) x z := by
      simp [S]
    by_contra hxy
    have hproper : S ≠ Finset.univ := by
      intro hs
      have hy : y ∈ S := by rw [hs]; exact Finset.mem_univ y
      exact hxy ((hmem y).mp hy)
    obtain ⟨u, hu, v, hv, huv⟩ := hc S ⟨x, (hmem x).mpr .refl⟩ hproper
    exact hv ((hmem v).mpr ((hmem u).mp hu |>.tail huv))
  · intro hc S hne hproper
    have hmissing : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hproper (Finset.eq_univ_of_forall h)
    obtain ⟨u, v, hu, hv, huv⟩ := exists_edge_leaving hc
      (show ∃ u, u ∈ (S : Set V) from hne) hmissing
    exact ⟨u, hu, v, hv, huv⟩

noncomputable def leaderCount {V : Type} [Fintype V] (leader : V → Bool) : Nat := by
  classical
  exact (Finset.univ.filter (fun v => leader v = true)).card

structure Admissible {V : Type} [Fintype V] (ell : Nat)
    (G : Nat → V → V → Nat) (leader : V → Bool) : Prop where
  positive : 0 < ell
  leaders : leaderCount leader = ell
  connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)

theorem Admissible.leaderCount_le_card {V : Type} [Fintype V] {ell : Nat}
    {G : Nat → V → V → Nat} {leader : V → Bool} (h : Admissible ell G leader) :
    ell ≤ Fintype.card V := by
  rw [← h.leaders]
  exact Finset.card_le_univ _

/-- One protocol is correct on every admissible order and leader count. -/
def Protocol.SolvesCounting {State : Type} (P : Protocol State) : Prop :=
  ∀ (V : Type) [Fintype V] (ell : Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool), Admissible ell G leader →
    (∀ t x s k, P.trace ell G leader t x = .halted s k → k = Fintype.card V) ∧
    (∃ t, ∀ x, ∃ s, P.trace ell G leader t x = .halted s (Fintype.card V))

/-- A common history across two admissible different orders prevents halting
for every universally correct protocol, including protocols with silent halts. -/
theorem universal_lower_bound {State V W : Type} [Fintype V] [Fintype W]
    (P : Protocol State) (correct : P.SolvesCounting)
    (ell : Nat) (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (leaderV : V → Bool) (leaderW : W → Bool)
    (validV : Admissible ell G leaderV) (validW : Admissible ell H leaderW)
    (t : Nat) (x : V) (y : W)
    (different : Fintype.card V ≠ Fintype.card W)
    (common : history G leaderV t x = history H leaderW t y) :
    ∃ s, P.trace ell G leaderV t x = .active s := by
  exact P.common_history_prevents_halting ell G H leaderV leaderW t x y common different
    (fun s k hk => (correct V ell G leaderV validV).1 t x s k hk)
    (fun s k hk => (correct W ell H leaderW validW).1 t y s k hk)

end Counting
