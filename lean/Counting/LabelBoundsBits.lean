import Counting.LabelBoundsAnchor

namespace Counting.Executable

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Binary lengths of every physical degree and multiplicity label, when
the per-round total number of arcs is at most 2^p. -/
theorem labels_size_of_arc_power (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (p : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ 2^p)
    (i : Nat) (inside : i < vista.nodes.size) :
    Nat.size (vista.node i).degree ≤ p+1 ∧
      (∀ old, Nat.size (countFrom (vista.node i) old) ≤ p+1) ∧
      (∀ edge ∈ (vista.node i).incoming, Nat.size edge.2 ≤ p+1) := by
  refine ⟨size_le_of_le_two_pow _ p (stored_labels_le G leader t observer vista valid depth physical _ mass i inside).1,
    fun old => size_le_of_le_two_pow _ p (countFrom_le_arc_bound G leader t observer vista valid depth physical _ mass i old inside),
    fun edge present => size_le_of_le_two_pow _ p (incoming_entry_le_arc_bound G leader t observer vista valid depth physical _ mass i inside edge present)⟩

/-- Actual anchor coefficients have at most p+3 numerator/denominator bits
under the total-arc bound 2^p. A separate sign bit costs at most one more. -/
theorem anchor_coefficient_size_of_arc_power (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (p : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ 2^p)
    (anchor leaders : Nat) (row : Equation) (member : row ∈ anchorRows vista anchor leaders)
    (coefficient : ℚ) (present : coefficient ∈ row.1.toList) :
    Nat.size coefficient.num.natAbs + Nat.size coefficient.den ≤ p+3 := by
  have bound := (physical_anchor_coefficients G leader t observer vista valid depth physical _ mass
    anchor leaders row member coefficient present).2.2
  simpa only [Nat.size_pow, Nat.add_assoc] using bound

/-- A per-bundle exponential bound gives a polynomial bit bound as well;
the n² possible ordered pairs contribute at most 2*size(n) extra bits. -/
theorem labels_size_of_bundle_power (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (p : Nat) (bundles : ∀ r, 0 < r → r ≤ t → ∀ x y, G r x y ≤ 2^p)
    (i : Nat) (inside : i < vista.nodes.size) :
    Nat.size (vista.node i).degree ≤ 2*Nat.size (Fintype.card V)+p+1 ∧
      ∀ old, Nat.size (countFrom (vista.node i) old) ≤ 2*Nat.size (Fintype.card V)+p+1 := by
  have mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ Fintype.card V^2 * 2^p :=
    fun r positive within => arcMass_le_of_bundle_bound G r (2^p) (bundles r positive within)
  have size := square_times_power_size (Fintype.card V) p
  exact ⟨(Nat.size_le_size (stored_labels_le G leader t observer vista valid depth physical _ mass i inside).1).trans size,
    fun old => (Nat.size_le_size (countFrom_le_arc_bound G leader t observer vista valid depth physical _ mass i old inside)).trans size⟩

/-- At the latest required counting horizon the actual DAG has at most 2n²
nodes and 2n³ sparse incoming entries. This is a representation bound, not
a runtime claim about the interpreter or arithmetic algorithms. -/
theorem counting_horizon_size (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (horizon : t ≤ 2*Fintype.card V-1) :
    vista.nodes.size ≤ 2 * Fintype.card V^2 ∧
      ((List.range vista.nodes.size).map (fun i => (vista.node i).incoming.length)).sum ≤ 2*Fintype.card V^3 := by
  have positive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨observer⟩
  have time : t+1 ≤ 2*Fintype.card V := by omega
  have nodes := nodes_size_le_depth_mul_card G leader t observer vista valid depth physical
  have entries := incoming_entries_le G leader t observer vista valid depth physical
  constructor
  · apply nodes.trans
    calc
      _ ≤ (2*Fintype.card V)*Fintype.card V := Nat.mul_le_mul_right _ time
      _ = _ := by ring
  · apply entries.trans
    calc
      _ ≤ (2*Fintype.card V)*Fintype.card V^2 := Nat.mul_le_mul_right _ time
      _ = _ := by ring

/-- Instantiating p by any polynomial expression, for example c*n^k,
gives the polynomial label length used by the machine-time bound in
MachineCountingRuntimeTheorems. -/
theorem polynomial_arc_label_bound (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (c k : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ 2^(c*Fintype.card V^k))
    (i : Nat) (inside : i < vista.nodes.size) :
    Nat.size (vista.node i).degree ≤ c*Fintype.card V^k+1 ∧
      (∀ old, Nat.size (countFrom (vista.node i) old) ≤ c*Fintype.card V^k+1) ∧
      (∀ edge ∈ (vista.node i).incoming, Nat.size edge.2 ≤ c*Fintype.card V^k+1) :=
  labels_size_of_arc_power G leader t observer vista valid depth physical _ mass i inside

end Counting.Executable
