import Counting.CountingSizeSparse
import Mathlib.Data.Nat.Size

namespace Counting.Executable
open scoped BigOperators

/-- The sum of binary bundle counts is used only as a mathematical measure. -/
def incomingWeight (node : Node) : Nat := (node.incoming.map Prod.snd).sum

theorem bundleMessages_card {A : Type} (value : Nat → A) (bundles : List (Nat × Nat)) :
    (bundleMessages value bundles).card = (bundles.map Prod.snd).sum := by
  induction bundles with
  | nil => rfl
  | cons edge rest ih => simp only [bundleMessages_cons, Multiset.card_add,
      Multiset.card_replicate, List.map_cons, List.sum_cons, ih]

theorem countFrom_le_weight (node : Node) (old : Nat) : countFrom node old ≤ incomingWeight node := by
  unfold countFrom incomingWeight
  generalize node.incoming = bundles
  induction bundles with
  | nil => simp
  | cons edge rest ih =>
    by_cases equal : edge.1 = old
    · simp [equal]
    · simp only [List.find?_cons, beq_eq_false_iff_ne.mpr equal,
        List.map_cons, List.sum_cons]
      omega

theorem incoming_entry_le_weight (node : Node) (edge : Nat × Nat) (present : edge ∈ node.incoming) :
    edge.2 ≤ incomingWeight node :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) edge.2 (List.mem_map.mpr ⟨edge, present, rfl⟩)

variable {V : Type} [Fintype V]

/-- Number of directed arcs with multiplicity in a physical round. -/
def arcMass (G : Nat → V → V → Nat) (r : Nat) : Nat := ∑ x, ∑ y, G r x y

theorem outgoing_le_arcMass (G : Nat → V → V → Nat) (r : Nat) (x : V) :
    (∑ y, G r x y) ≤ arcMass G r := by
  unfold arcMass
  exact Finset.single_le_sum (f := fun z : V => ∑ y, G r z y)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

theorem incoming_card_le_arcMass {A : Type} (G : Nat → V → V → Nat)
    (state : V → A) (r : Nat) (receiver : V) :
    (Counting.incoming (G r) state receiver).card ≤ arcMass G r := by
  rw [Counting.incoming, Multiset.card_sum]
  simp only [Multiset.card_replicate]
  apply Finset.sum_le_sum
  intro sender _
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ receiver)

variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Every stored outdegree and every sum of incoming multiplicities is
bounded by the actual round's arc mass. Level zero has both labels zero. -/
theorem stored_labels_le (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (i : Nat) (inside : i < vista.nodes.size) :
    (vista.node i).degree ≤ M ∧ incomingWeight (vista.node i) ≤ M := by
  by_cases zero : (vista.node i).level = 0
  · obtain ⟨_, degree, incoming⟩ := nodeValid_zero vista i (nodeValid_of_valid vista valid i inside) zero
    simp [degree, incomingWeight, incoming]
  · obtain ⟨r, level⟩ := Nat.exists_eq_succ_of_ne_zero zero
    obtain ⟨agent, equal⟩ := stored_node_realized G leader t observer vista valid depth physical i inside
    rw [level] at equal
    have within : r+1 ≤ t := by have := stored_level_le_bottom vista valid i inside; omega
    have degree : (vista.node i).degree = ∑ y, G (r+1) agent y :=
      congrArg (fun H : Counting.FullHistory (r+1) => H.2.1) equal
    have incoming : incomingWeight (vista.node i) =
        (Counting.incoming (G (r+1)) (Counting.history G leader r) agent).card := by
      have count := congrArg (fun H : Counting.FullHistory (r+1) => H.2.2.card) equal
      simpa only [decodeNode, Counting.history, bundleMessages_card, incomingWeight] using count
    exact ⟨degree ▸ (outgoing_le_arcMass G (r+1) agent).trans (mass (r+1) (by omega) within),
      incoming ▸ (incoming_card_le_arcMass G _ (r+1) agent).trans (mass (r+1) (by omega) within)⟩

theorem countFrom_le_arc_bound (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (i old : Nat) (inside : i < vista.nodes.size) :
    countFrom (vista.node i) old ≤ M :=
  (countFrom_le_weight _ _).trans (stored_labels_le G leader t observer vista valid depth physical M mass i inside).2

theorem incoming_entry_le_arc_bound (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (i : Nat) (inside : i < vista.nodes.size) (edge : Nat × Nat) (present : edge ∈ (vista.node i).incoming) :
    edge.2 ≤ M :=
  (incoming_entry_le_weight _ _ present).trans
    (stored_labels_le G leader t observer vista valid depth physical M mass i inside).2

/-- The bound also follows from a bound on each individual arc bundle. -/
theorem arcMass_le_of_bundle_bound (r E : Nat) (bound : ∀ x y, G r x y ≤ E) :
    arcMass G r ≤ Fintype.card V ^ 2 * E := by
  have all := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ => bound x y))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at all
  unfold arcMass
  calc
    _ ≤ Fintype.card V * (Fintype.card V * E) := all
    _ = _ := by ring

end Counting.Executable
