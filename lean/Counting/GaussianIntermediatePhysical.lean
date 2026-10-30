import Counting.GaussianIntermediateArithmetic
import Counting.GaussianPhysicalBounds

/-! Polynomial bit-length envelopes for the actual stored Gaussian run,
including rejected candidates and every prefix of transcript replay.
These are space/operand bounds, not machine-step complexity claims. -/
namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem Counting.Executable

theorem size_max_one_le (value : Nat) : (max value 1).size ≤ value.size+1 := by
  rcases le_total value 1 with small | large
  · rw [max_eq_right small]
    simp
  · rw [max_eq_left large]
    omega

theorem intermediateBound_normal_le (width count M : Nat) :
    intermediateBound width (count*M^2) ≤
      2*(width*(width.size+count.size+2*M.size+2)+1) := by
  have normal := normal_envelope_bits count M
  have padded := size_max_one_le (count*M^2)
  unfold intermediateBound
  apply Nat.mul_le_mul_left 2
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left width (by omega)

theorem normalSystem_intermediate_polynomial_bits (width : Nat) (rows : List Equation) (M : Nat)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧ (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M)
    (length : Nat) (row : Fin width) (column : Option (Fin width)) :
    rationalBits (augmented (StoredGaussian.replay (normalSystem width rows)
      ((StoredGaussian.runGaussian (normalSystem width rows)).opsRev.reverse.take length)) row column) ≤
      2*(width*(width.size+rows.length.size+2*M.size+2)+1) :=
  (normalSystem_all_intermediate_bits width rows M coeff rhs length row column).trans
    (intermediateBound_normal_le width rows.length M)

theorem OperationBound.mono {q left right : Nat} {op : RowOp q}
    (bound : OperationBound left op) (increase : left ≤ right) : OperationBound right op := by
  cases op with
  | swap => trivial
  | scale => exact bound.trans increase
  | add => exact bound.trans increase

theorem normalSystem_operation_polynomial_bits (width : Nat) (rows : List Equation) (M : Nat)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧ (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M)
    (op : RowOp width) (emitted : op ∈ (StoredGaussian.runGaussian (normalSystem width rows)).opsRev) :
    OperationBound (2*(width*(width.size+rows.length.size+2*M.size+2)+1)) op :=
  (normalSystem_all_operation_bits width rows M coeff rhs op emitted).mono
    (intermediateBound_normal_le width rows.length M)

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Every stored coefficient and right-hand-side value throughout the
actual solve has a polynomial bit-length bound in population and label
length. The candidate need not be accepted or have a nonsingular system. -/
theorem physical_anchor_intermediate_bits (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (anchor leaders length : Nat) (row : Fin (levelNodes vista anchor).length)
    (column : Option (Fin (levelNodes vista anchor).length)) :
    rationalBits (augmented (StoredGaussian.replay
      (normalSystem (levelNodes vista anchor).length (anchorRows vista anchor leaders))
      ((StoredGaussian.runGaussian (normalSystem (levelNodes vista anchor).length
        (anchorRows vista anchor leaders))).opsRev.reverse.take length)) row column) ≤
      2*(Fintype.card V*(Nat.size (Fintype.card V)+(Fintype.card V+1).size+
        2*(max (max (2*M) 1) leaders).size+2)+1) := by
  obtain ⟨coeff, rhs⟩ := anchor_rows_integral_bounded vista anchor leaders M
    (levelNodes vista anchor).length
    (fun j inside => (stored_labels_le G leader t observer vista valid depth physical M mass j inside).1)
    (fun j inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass j old inside)
  have bound := normalSystem_intermediate_polynomial_bits _ _ _ coeff rhs length row column
  have width := levelNodes_length_le_card G leader t observer vista valid depth physical anchor
  have widthBits := Nat.size_le_size width
  have rowBits := Nat.size_le_size (physical_anchor_rows_length G leader t observer vista valid depth physical anchor leaders)
  apply bound.trans
  apply Nat.mul_le_mul_left 2
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul width (by omega)

/-- The inverse pivots and row-addition multipliers written into the
actual certificate obey the same envelope as matrix entries. -/
theorem physical_anchor_operation_bits (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (anchor leaders : Nat) (op : RowOp (levelNodes vista anchor).length)
    (emitted : op ∈ (StoredGaussian.runGaussian
      (normalSystem (levelNodes vista anchor).length (anchorRows vista anchor leaders))).opsRev) :
    OperationBound
      (2*(Fintype.card V*(Nat.size (Fintype.card V)+(Fintype.card V+1).size+
        2*(max (max (2*M) 1) leaders).size+2)+1)) op := by
  obtain ⟨coeff, rhs⟩ := anchor_rows_integral_bounded vista anchor leaders M
    (levelNodes vista anchor).length
    (fun j inside => (stored_labels_le G leader t observer vista valid depth physical M mass j inside).1)
    (fun j inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass j old inside)
  have bound := normalSystem_operation_polynomial_bits _ _ _ coeff rhs op emitted
  apply bound.mono
  have width := levelNodes_length_le_card G leader t observer vista valid depth physical anchor
  have widthBits := Nat.size_le_size width
  have rowBits := Nat.size_le_size (physical_anchor_rows_length G leader t observer vista valid depth physical anchor leaders)
  apply Nat.mul_le_mul_left 2
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul width (by omega)

end Counting.GaussianBits
