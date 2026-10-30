import Counting.StackGaussianRhsFinish
import Counting.StackMatrixSwapBounds
import Counting.MachineMatrixSwapGaussian

namespace Counting.StackMachine.GaussianRhs
open Routine DirectedCounting.VerifiedGaussianAnchorSolver

theorem selected_sequence_length (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) :
    (Encoding.sequence (Encoding.framed Encoding.rational) values).length ≤
      (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length := by
  induction selected with
  | nil => rfl
  | @cons row value rows values selected tail ih =>
    have valueBound := RowScale.member_row_length_le row value (List.mem_of_getElem? selected)
    simp only [Encoding.sequence,List.length_append,Encoding.framed_length]
    omega

/-- The final-column extraction is quadratic in the actual serialized
matrix and its explicit unary column index. -/
theorem extract_executes_polynomial (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) :
    ∃ time ≤ 2000*((Encoding.rationalMatrix.encode rows).length+column+2)^2,
      Executes extract (state (Encoding.rationalMatrix.encode rows) [] column (List.replicate rows.length true) []) time
        (state [] (Encoding.rationalRow.encode values) column [] []) := by
  let size := (Encoding.rationalMatrix.encode rows).length
  obtain ⟨time,bounded,ran⟩ := extract_executes rows values column selected size
    (fun row present => Encoding.framedList_member_length_le Encoding.rationalRow rows row present)
  have valuesBound := selected_sequence_length rows values column selected
  have countBound := Encoding.framedList_count_le Encoding.rationalRow rows
  have splitSize : size=(Encoding.natural.encode rows.length).length+
      (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows).length := List.length_append
  have bitsBound : rows.length.bits.length ≤ (Encoding.natural.encode rows.length).length := by
    rw [Encoding.natural_length,Encoding.bits_length]
    omega
  change rows.length ≤ size at countBound
  have productBound := Nat.mul_le_mul countBound
    (show 100*(size+column+2)+2 ≤ 102*(size+column+2) by omega)
  refine ⟨time,?_,ran⟩
  change _≤2000*(size+column+2)^2
  nlinarith

theorem augmented_selected {q : Nat} (system : RationalSystem q) :
    List.Forall₂ (fun row value => row[q]?=some value)
      (StoredGaussian.augmentedMatrix system) (List.ofFn system.rhs) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,?_⟩
  intro i first second
  simp [StoredGaussian.augmentedMatrix,StoredGaussian.augmentedRow]

theorem extract_augmented {q : Nat} (system : RationalSystem q) :
    ∃ time ≤ 2000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+2)^2,
      Executes extract
        (state (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] q (List.replicate q true) []) time
        (state [] (Encoding.rationalRow.encode (List.ofFn system.rhs)) q [] []) := by
  simpa only [StoredGaussian.augmentedMatrix_length] using
    extract_executes_polynomial (StoredGaussian.augmentedMatrix system) (List.ofFn system.rhs) q (augmented_selected system)

end Counting.StackMachine.GaussianRhs
