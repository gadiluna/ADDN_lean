import Counting.GaussianOutputBounds
import Counting.CountingSize

namespace Counting.GaussianBits
open Counting.Executable

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- The actual rectangular anchor system has at most n+1 equations,
including its one leader-normalization row. -/
theorem physical_anchor_rows_length (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (anchor leaders : Nat) :
    (anchorRows vista anchor leaders).length ≤ Fintype.card V + 1 := by
  have bound := levelNodes_length_le_card G leader t observer vista valid depth physical (anchor-1)
  simpa only [anchorRows, List.length_append, List.length_map, List.length_singleton] using
    Nat.add_le_add_right bound 1

/-- The integral normal system produced on any physical vista has only
polynomial-length entries; no acceptance or exhaustive-anchor hypothesis
is needed for this preprocessing bound. -/
theorem physical_normal_system_bits (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (anchor leaders width : Nat) :
    (∀ i j, ((normalSystem width (anchorRows vista anchor leaders)).coeff i j).den = 1 ∧
      ((normalSystem width (anchorRows vista anchor leaders)).coeff i j).num.natAbs.size ≤
        (Fintype.card V+1).size + 2*(max (max (2*M) 1) leaders).size + 1) ∧
    (∀ i, ((normalSystem width (anchorRows vista anchor leaders)).rhs i).den = 1 ∧
      ((normalSystem width (anchorRows vista anchor leaders)).rhs i).num.natAbs.size ≤
        (Fintype.card V+1).size + 2*(max (max (2*M) 1) leaders).size + 1) := by
  obtain ⟨left, right⟩ := anchor_normal_system_bits vista anchor leaders M width
    (fun i inside => (stored_labels_le G leader t observer vista valid depth physical M mass i inside).1)
    (fun i inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass i old inside)
  have size := Nat.size_le_size (physical_anchor_rows_length G leader t observer vista valid depth physical anchor leaders)
  exact ⟨fun i j => ⟨(left i j).1, by have := (left i j).2; omega⟩,
    fun i => ⟨(right i).1, by have := (right i).2; omega⟩⟩

/-- Every successful actual anchor solve has a polynomial-size rational
answer. Intermediate Gaussian entries and machine running time are not
asserted by this output-size theorem. -/
theorem physical_anchor_solution_bits (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (anchor leaders : Nat) (result : Array ℚ)
    (accepted : solveLinear? (levelNodes vista anchor).length (anchorRows vista anchor leaders) = some result)
    (i : Fin (levelNodes vista anchor).length) :
    (arrayVector (levelNodes vista anchor).length result i).num.natAbs.size +
      (arrayVector (levelNodes vista anchor).length result i).den.size ≤
      2*(Fintype.card V*(Nat.size (Fintype.card V) + (Fintype.card V+1).size +
        2*(max (max (2*M) 1) leaders).size + 1)+1) := by
  obtain ⟨coeff, rhs⟩ := anchor_rows_integral_bounded vista anchor leaders M
    (levelNodes vista anchor).length
    (fun j inside => (stored_labels_le G leader t observer vista valid depth physical M mass j inside).1)
    (fun j inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass j old inside)
  have bound := solveLinear_output_bits _ _ _ result accepted coeff rhs i
  have width := levelNodes_length_le_card G leader t observer vista valid depth physical anchor
  have widthBits := Nat.size_le_size width
  have rowBits := Nat.size_le_size (physical_anchor_rows_length G leader t observer vista valid depth physical anchor leaders)
  apply bound.trans
  apply Nat.mul_le_mul_left 2
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul width (by omega)

end Counting.GaussianBits
