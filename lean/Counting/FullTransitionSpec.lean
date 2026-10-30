import Counting.RealizabilityConstructionMany
import Counting.RealizabilityConstructionConnected

/-! Full-level transition data. A realization fixes every agent's new class,
outdegree, and number of received arcs from each old parent class. -/

namespace Counting.FullTransition
open DirectedCounting Relation

structure Data (U W : Type*) where
  parent : W → U
  degree : W → Nat
  red : U → W → Nat

namespace Data
variable {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U]

def Arc (d : Data U W) (v w : W) : Prop :=
  0 < d.degree v ∧ 0 < d.red (d.parent v) w

def Flow (d : Data U W) (tag : A → W) : Prop :=
  ∀ u, (∑ a, if d.parent (tag a) = u then d.degree (tag a) else 0) =
    ∑ a, d.red u (tag a)

structure Realizes (d : Data U W) (tag : A → W) (E : A → A → Nat) : Prop where
  connected : StronglyConnected (fun a b => 0 < E a b)
  degrees : ∀ a, (∑ b, E a b) = d.degree (tag a)
  receipts : ∀ u b, (∑ a, if d.parent (tag a) = u then E a b else 0) = d.red u (tag b)

def Conditions (d : Data U W) : Prop :=
  (∀ v, 0 < d.degree v) ∧ (∀ v, 0 < ∑ u, d.red u v) ∧ StronglyConnected d.Arc

variable (d : Data U W) {tag : A → W} {E : A → A → Nat}

omit [Fintype U] in
theorem Realizes.arc_of_positive (h : d.Realizes tag E) {a b : A} (edge : 0 < E a b) :
    d.Arc (tag a) (tag b) := by
  classical
  constructor
  · rw [← h.degrees a]
    exact edge.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  · rw [← h.receipts (d.parent (tag a)) b]
    apply Finset.sum_pos_iff.mpr
    exact ⟨a, Finset.mem_univ a, by simpa using edge⟩

omit [Fintype U] in
theorem Realizes.node_connected (h : d.Realizes tag E) (represented : Function.Surjective tag) :
    StronglyConnected d.Arc := by
  intro v w
  obtain ⟨a, rfl⟩ := represented v
  obtain ⟨b, rfl⟩ := represented w
  have project : ∀ x y, ReflTransGen (fun x y => 0 < E x y) x y →
      ReflTransGen d.Arc (tag x) (tag y) := by
    intro x y path
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail (h.arc_of_positive d edge)
  exact project a b (h.connected a b)

theorem Realizes.necessary (h : d.Realizes tag E) (represented : Function.Surjective tag)
    (many : 1 < Fintype.card A) : d.Conditions := by
  classical
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp many
  refine ⟨?_, ?_, h.node_connected d represented⟩
  · intro v
    obtain ⟨a, rfl⟩ := represented v
    obtain ⟨b, different⟩ := exists_ne a
    obtain ⟨x, y, hx, _, edge⟩ := exists_edge_leaving h.connected
      (Q := {x | x = a}) ⟨a, rfl⟩ ⟨b, different⟩
    subst x
    exact (h.arc_of_positive d edge).1
  · intro v
    obtain ⟨a, rfl⟩ := represented v
    obtain ⟨b, different⟩ := exists_ne a
    obtain ⟨x, y, _, hy, edge⟩ := exists_edge_leaving h.connected
      (Q := {x | x ≠ a}) ⟨b, different⟩ ⟨a, by simp⟩
    have eq : y = a := by simpa using hy
    subst y
    exact Finset.sum_pos_iff.mpr
      ⟨d.parent (tag x), Finset.mem_univ _, (h.arc_of_positive d edge).2⟩

end Data
end Counting.FullTransition
