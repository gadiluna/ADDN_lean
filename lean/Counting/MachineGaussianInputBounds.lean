import Counting.MachineGaussian

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

theorem augmented_entry_encoded_le {q : Nat} (system : RationalSystem q) (row : Fin q) (column : Option (Fin q)) :
    (Encoding.rational.encode (augmented system row column)).length ≤
      (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length := by
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow (StoredGaussian.augmentedMatrix system)
    (StoredGaussian.augmentedRow system row) (List.mem_ofFn.mpr ⟨row,rfl⟩)
  have member : augmented system row column∈StoredGaussian.augmentedRow system row := by
    cases column with
    | none => simp [augmented,StoredGaussian.augmentedRow]
    | some column =>
      simp only [augmented,StoredGaussian.augmentedRow,List.mem_append,List.mem_ofFn,List.mem_singleton]
      exact Or.inl ⟨column,rfl⟩
  exact (StackMachine.RowScale.member_row_length_le _ _ member).trans rowBound

theorem augmented_dimension_le_input {q : Nat} (system : RationalSystem q) :
    q ≤ (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length := by
  simpa only [StoredGaussian.augmentedMatrix_length,Encoding.rationalMatrix] using
    Encoding.framedList_count_le Encoding.rationalRow (StoredGaussian.augmentedMatrix system)

theorem augmented_numerator_lt_input_power {q : Nat} (system : RationalSystem q) (row : Fin q) (column : Option (Fin q)) :
    (augmented system row column).num.natAbs <
      2^((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length) := by
  have encoded := augmented_entry_encoded_le system row column
  rw [Encoding.rational_length] at encoded
  apply Nat.size_le.mp
  omega

/-- Both dimension and numerical label bounds follow from the actual
framed input, including the degenerate empty system. -/
theorem intermediateBound_input_le {q : Nat} (system : RationalSystem q) :
    intermediateBound q (2^((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length)) ≤
      6*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)^2 := by
  let length := (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length
  have dimension := augmented_dimension_le_input system
  change q ≤ length at dimension
  have dimensionBits : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have powerPositive : 1 ≤ 2^length := Nat.one_le_pow' length 1
  change intermediateBound q (2^length) ≤ 6*(length+1)^2
  simp only [intermediateBound,max_eq_left powerPositive,Nat.size_pow]
  nlinarith

end Counting.GaussianBits
