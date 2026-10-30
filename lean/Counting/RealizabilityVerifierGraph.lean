import DirectedCountingFormalization.Connectivity
import Mathlib.Tactic

namespace Counting.RealizabilityVerifier
open DirectedCounting

/-- A finite reachability checker. The carrier here is the compact graph
of certificate types, never the population described by the counts. -/
def reachStep {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun v => ∃ u, u ∈ S ∧ arc u v = true)

def reachable {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (source : V) : ℕ → Finset V
  | 0 => {source}
  | k + 1 => reachStep arc (reachable arc source k)

def connectedCheck {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) : Bool :=
  decide (∀ source, reachable arc source (Fintype.card V) = Finset.univ)

theorem mem_reachStep {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (S : Finset V) (v : V) :
    v ∈ reachStep arc S ↔ v ∈ S ∨ ∃ u, u ∈ S ∧ arc u v = true := by
  simp [reachStep]

theorem reachable_mono {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (source : V) {k l : ℕ} (bound : k ≤ l) :
    reachable arc source k ⊆ reachable arc source l := by
  induction bound with
  | refl => exact Finset.Subset.refl _
  | @step l bound ih => exact ih.trans (by intro v hv; exact (mem_reachStep _ _ _).mpr (Or.inl hv))

theorem reachable_sound {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (source : V) (k : ℕ) :
    ∀ v ∈ reachable arc source k, Relation.ReflTransGen (fun a b => arc a b = true) source v := by
  induction k with
  | zero =>
      intro v hv
      have same : v = source := by simpa [reachable] using hv
      subst v
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro v hv
      rcases (mem_reachStep _ _ _).mp hv with old | ⟨u, hu, edge⟩
      · exact ih v old
      · exact (ih u hu).tail edge

theorem connectedCheck_sound {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (accepted : connectedCheck arc = true) :
    StronglyConnected (fun a b => arc a b = true) := by
  have all : ∀ source, reachable arc source (Fintype.card V) = Finset.univ := by
    simpa only [connectedCheck, decide_eq_true_eq] using accepted
  intro a b
  apply reachable_sound arc a (Fintype.card V) b
  rw [all a]
  exact Finset.mem_univ b

theorem reachStep_grows {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (connected : StronglyConnected (fun a b => arc a b = true))
    (S : Finset V) (nonempty : S.Nonempty) (proper : S ≠ Finset.univ) :
    S.card < (reachStep arc S).card := by
  have outside : ∃ v, v ∉ S := by
    by_contra no
    apply proper
    exact Finset.eq_univ_of_forall (by simpa using no)
  obtain ⟨a, ha⟩ := nonempty
  obtain ⟨b, hb⟩ := outside
  obtain ⟨u, v, hu, hv, edge⟩ := exists_edge_leaving connected ⟨a, ha⟩ ⟨b, hb⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  refine ⟨v, hv, ?_⟩
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | old
  · exact (mem_reachStep _ _ _).mpr (Or.inr ⟨u, hu, edge⟩)
  · exact (mem_reachStep _ _ _).mpr (Or.inl old)

theorem reachable_complete {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) (connected : StronglyConnected (fun a b => arc a b = true))
    (source : V) : reachable arc source (Fintype.card V) = Finset.univ := by
  by_contra no
  have proper : ∀ k, k ≤ Fintype.card V → reachable arc source k ≠ Finset.univ := by
    intro k hk equal
    apply no
    apply Finset.eq_univ_of_forall
    intro v
    exact reachable_mono arc source hk (by simp [equal])
  have lower : ∀ k, k ≤ Fintype.card V → k + 1 ≤ (reachable arc source k).card := by
    intro k
    induction k with
    | zero => intro _; simp [reachable]
    | succ k ih =>
        intro hk
        have hk' : k ≤ Fintype.card V := by omega
        have nonempty : (reachable arc source k).Nonempty :=
          ⟨source, reachable_mono arc source (Nat.zero_le k) (by simp [reachable])⟩
        have grows := reachStep_grows arc connected _ nonempty (proper k hk')
        have previous := ih hk'
        change k + 1 + 1 ≤ (reachStep arc (reachable arc source k)).card
        omega
  have tooLarge := lower (Fintype.card V) (le_refl _)
  have atMost := Finset.card_le_univ (reachable arc source (Fintype.card V))
  omega

theorem connectedCheck_iff {V : Type*} [Fintype V] [DecidableEq V]
    (arc : V → V → Bool) :
    connectedCheck arc = true ↔ StronglyConnected (fun a b => arc a b = true) := by
  refine ⟨connectedCheck_sound arc, fun connected => ?_⟩
  apply decide_eq_true
  exact reachable_complete arc connected

/-- Connectivity is invariant under a bijection of compact graph types. -/
theorem connected_equiv {V W : Type*} (e : V ≃ W) (a : V → V → Prop) (b : W → W → Prop)
    (edges : ∀ u v, a u v ↔ b (e u) (e v)) : StronglyConnected a ↔ StronglyConnected b := by
  constructor
  · intro connected u v
    have path := (connected (e.symm u) (e.symm v)).lift e
      (fun x y h => (edges x y).mp h)
    simpa only [Function.onFun, e.apply_symm_apply] using path
  · intro connected u v
    have path := (connected (e u) (e v)).lift e.symm (by
      intro x y h
      apply (edges (e.symm x) (e.symm y)).mpr
      simpa only [e.apply_symm_apply] using h)
    simpa only [Function.onFun, e.symm_apply_apply] using path

end Counting.RealizabilityVerifier
