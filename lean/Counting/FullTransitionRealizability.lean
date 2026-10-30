import Counting.FullTransitionConstruction

/-! The paper's full transition lemma, with explicit positive fiber sizes.
`Agents anonymity` contains exactly `anonymity v` agents in every new class. -/

namespace Counting.FullTransition
open DirectedCounting

namespace Data
variable {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U]

omit [Fintype U] in
/-- A single agent realizes all balanced requirements using loops, including
the case of zero loops. No positive-degree assumption is needed. -/
theorem singleton (d : Data U W) {tag : A → W} (flow : d.Flow tag)
    (one : Fintype.card A = 1) : ∃ E, d.Realizes tag E := by
  classical
  obtain ⟨a₀, all⟩ := Fintype.card_eq_one_iff.mp one
  letI : Unique A := ⟨⟨a₀⟩, all⟩
  refine ⟨fun a _ => d.degree (tag a), ?_, ?_, ?_⟩
  · intro a b
    have eq : a = b := Subsingleton.elim _ _
    subst b
    exact .refl
  · intro a
    simp
  · intro u b
    have eq : b = a₀ := all b
    subst b
    simpa [show (default : A) = a₀ from rfl] using flow u

theorem realizable_iff (d : Data U W) {tag : A → W}
    (flow : d.Flow tag) (represented : Function.Surjective tag)
    (many : 1 < Fintype.card A) : (∃ E, d.Realizes tag E) ↔ d.Conditions := by
  letI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  exact ⟨fun ⟨_, h⟩ => h.necessary d represented many, d.sufficient flow represented⟩

end Data

abbrev Agents {W : Type*} (anonymity : W → Nat) := Σ v, Fin (anonymity v)

def agentsFiberEquiv {W : Type*} (anonymity : W → Nat) (v : W) :
    {a : Agents anonymity // a.1 = v} ≃ Fin (anonymity v) where
  toFun a := Fin.cast (congrArg anonymity a.property) a.val.2
  invFun i := ⟨⟨v, i⟩, rfl⟩
  left_inv := by rintro ⟨⟨w, i⟩, eq⟩; cases eq; rfl
  right_inv := by intro i; rfl

theorem agents_fiber_card {W : Type*} (anonymity : W → Nat) (v : W) :
    Nat.card {a : Agents anonymity // a.1 = v} = anonymity v := by
  simpa using Nat.card_congr (agentsFiberEquiv anonymity v)

theorem agents_card {W : Type*} [Fintype W] (anonymity : W → Nat) :
    Fintype.card (Agents anonymity) = ∑ v, anonymity v := by
  simp [Agents, Fintype.card_sigma]

theorem agents_represented {W : Type*} (anonymity : W → Nat)
    (positive : ∀ v, 0 < anonymity v) : Function.Surjective (Sigma.fst : Agents anonymity → W) :=
  fun v => ⟨⟨v, ⟨0, positive v⟩⟩, rfl⟩

namespace Data
variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U]

/-- The paper's flow equation, with the fiber size explicitly multiplying
each agent's degree or receipt. -/
def WeightedFlow (d : Data U W) (anonymity : W → Nat) : Prop :=
  ∀ u, (∑ v, if d.parent v = u then anonymity v * d.degree v else 0) =
    ∑ v, anonymity v * d.red u v

omit [Fintype U] in
theorem weightedFlow_iff (d : Data U W) (anonymity : W → Nat) :
    d.WeightedFlow anonymity ↔ d.Flow (Sigma.fst : Agents anonymity → W) := by
  simp [WeightedFlow, Flow, Fintype.sum_sigma]

/-- **Realizing a transition**, for more than one agent: with positive
anonymities and balanced flow, a strongly connected round exists exactly
under the three conditions stated in the manuscript. -/
theorem realizing_transition (d : Data U W) (anonymity : W → Nat)
    (positive : ∀ v, 0 < anonymity v) (flow : d.WeightedFlow anonymity)
    (many : 1 < ∑ v, anonymity v) :
    (∃ E : Agents anonymity → Agents anonymity → Nat, d.Realizes Sigma.fst E) ↔
      d.Conditions := by
  exact d.realizable_iff ((d.weightedFlow_iff anonymity).mp flow)
    (agents_represented anonymity positive) (by simpa [agents_card] using many)

omit [Fintype U] in
/-- **Realizing a transition**, the one-agent clause: balance alone suffices. -/
theorem realizing_transition_singleton (d : Data U W) (anonymity : W → Nat)
    (flow : d.WeightedFlow anonymity) (one : (∑ v, anonymity v) = 1) :
    ∃ E : Agents anonymity → Agents anonymity → Nat, d.Realizes Sigma.fst E := by
  exact d.singleton ((d.weightedFlow_iff anonymity).mp flow) (by simpa [agents_card] using one)

end Data
end Counting.FullTransition
