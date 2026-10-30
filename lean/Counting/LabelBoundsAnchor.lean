import Counting.LabelBounds
import Counting.LabelBoundsArithmetic

namespace Counting.Executable

/-- Bounds for the exact array coefficients constructed by anchorRows, before
Gaussian elimination. Denominators are one, including the normalization row. -/
theorem anchorRows_coefficients (vista : Vista) (anchor leaders M : Nat)
    (degreeBound : ∀ i, i < vista.nodes.size → (vista.node i).degree ≤ M)
    (redBound : ∀ i, i < vista.nodes.size → ∀ old, countFrom (vista.node i) old ≤ M)
    (row : Equation) (member : row ∈ anchorRows vista anchor leaders)
    (coefficient : ℚ) (present : coefficient ∈ row.1.toList) :
    coefficient.den = 1 ∧ coefficient.num.natAbs ≤ max (2*M) 1 ∧
      Nat.size coefficient.num.natAbs + Nat.size coefficient.den ≤ Nat.size M+2 := by
  unfold anchorRows at member
  rcases List.mem_append.mp member with flow | normalize
  · obtain ⟨old, _, rfl⟩ := List.mem_map.mp flow
    obtain ⟨i, inside, rfl⟩ := List.mem_map.mp present
    have index : i < vista.nodes.size := by
      exact List.mem_range.mp (List.mem_of_mem_filter inside)
    let b := if (vista.node i).parent == some old then (vista.node i).degree else 0
    have bound : b ≤ M := by dsimp [b]; split <;> simp_all
    obtain ⟨den, num⟩ := rational_difference_bound _ _ M (redBound i index old) bound
    exact ⟨den, num.trans (le_max_left _ _), rational_difference_bits _ _ M (redBound i index old) bound⟩
  · have equal : row = ((levelNodes vista anchor |>.map
        (fun i => if (vista.node i).leader then (1 : ℚ) else 0)).toArray, (leaders : ℚ)) := by
      simpa only [List.mem_singleton] using normalize
    rw [equal] at present
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp present
    cases (vista.node i).leader <;> simp

theorem anchorRows_rhs (vista : Vista) (anchor leaders : Nat)
    (row : Equation) (member : row ∈ anchorRows vista anchor leaders) :
    row.2.den = 1 ∧ row.2.num.natAbs ≤ leaders ∧
      Nat.size row.2.num.natAbs + Nat.size row.2.den ≤ Nat.size leaders+1 := by
  unfold anchorRows at member
  rcases List.mem_append.mp member with flow | normalize
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp flow
    simp
  · simp only [List.mem_singleton] at normalize
    rw [normalize]
    simp

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Physical refinement supplies the bounds for every entry of the actual
executable anchor matrix. This is independent of which anchor is selected. -/
theorem physical_anchor_coefficients (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (anchor leaders : Nat) (row : Equation) (member : row ∈ anchorRows vista anchor leaders)
    (coefficient : ℚ) (present : coefficient ∈ row.1.toList) :
    coefficient.den = 1 ∧ coefficient.num.natAbs ≤ max (2*M) 1 ∧
      Nat.size coefficient.num.natAbs + Nat.size coefficient.den ≤ Nat.size M+2 :=
  anchorRows_coefficients vista anchor leaders M
    (fun i inside => (stored_labels_le G leader t observer vista valid depth physical M mass i inside).1)
    (fun i inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass i old inside)
    row member coefficient present

end Counting.Executable
