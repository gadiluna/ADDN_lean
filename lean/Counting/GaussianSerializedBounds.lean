import Counting.GaussianIntermediateRun
import Counting.EncodingGaussianOperation
import Counting.MachineMatrixSwapGaussian

/-! Bounds for the actual framed matrix and operation-stream representations.
These use the uniform minor bounds for actual Gaussian prefixes, rather than
iterating a local arithmetic size estimate at each elimination step. -/
namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
open DirectedCounting.GaussianGeneratorCompleteness
open StoredGaussian
variable {q : Nat}

theorem encoded_sequence_length_le {α : Type} (codec : Encoding.Codec α)
    (values : List α) (bound : Nat)
    (bounded : ∀ value ∈ values,(codec.encode value).length ≤ bound) :
    (Encoding.sequence codec values).length ≤ values.length*bound := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons value rest ih =>
    have head := bounded value List.mem_cons_self
    have tail := ih (fun a ha => bounded a (List.mem_cons_of_mem _ ha))
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    nlinarith

theorem augmentedRow_bits (system : RationalSystem q) (bound : Nat)
    (bounded : SystemBound bound system) (row : Fin q) :
    ∀ value ∈ augmentedRow system row,rationalBits value ≤ bound := by
  intro value member
  simp only [augmentedRow,List.mem_append,List.mem_ofFn,List.mem_singleton] at member
  rcases member with ⟨column,rfl⟩ | rfl
  · exact bounded row (some column)
  · exact bounded row none

theorem rationalRow_encoded_bound (row : List Rat) (bound : Nat)
    (bounded : ∀ value ∈ row,rationalBits value ≤ bound) :
    (Encoding.rationalRow.encode row).length ≤ 10*(row.length+1)*(bound+1) := by
  have fields := encoded_sequence_length_le (Encoding.framed Encoding.rational) row (4*bound+7) (by
    intro value member
    have h := bounded value member
    simp only [Encoding.framed_length,Encoding.rational_length]
    dsimp only [rationalBits] at h
    omega)
  have size := (show row.length.size ≤ row.length from Nat.size_le.mpr Nat.lt_two_pow_self)
  change (Encoding.natural.encode row.length++Encoding.sequence (Encoding.framed Encoding.rational) row).length ≤ _
  simp only [List.length_append,Encoding.natural_length]
  nlinarith

theorem augmentedMatrix_encoded_bound (system : RationalSystem q) (bound : Nat)
    (bounded : SystemBound bound system) :
    (Encoding.rationalMatrix.encode (augmentedMatrix system)).length ≤ 40*(q+1)^2*(bound+1) := by
  have rows : ∀ row ∈ augmentedMatrix system,
      (Encoding.rationalRow.encode row).length ≤ 10*(q+2)*(bound+1) := by
    intro row member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    simpa only [augmentedRow_length] using
      rationalRow_encoded_bound (augmentedRow system index) bound (augmentedRow_bits system bound bounded index)
  have fields := encoded_sequence_length_le (Encoding.framed Encoding.rationalRow)
    (augmentedMatrix system) (20*(q+2)*(bound+1)+1) (by
      intro row member
      rw [Encoding.framed_length]
      have h := rows row member
      nlinarith)
  simp only [augmentedMatrix_length] at fields
  have size := (show q.size ≤ q from Nat.size_le.mpr Nat.lt_two_pow_self)
  change (Encoding.natural.encode (augmentedMatrix system).length++
    Encoding.sequence (Encoding.framed Encoding.rationalRow) (augmentedMatrix system)).length ≤ _
  simp only [List.length_append,Encoding.natural_length,augmentedMatrix_length]
  nlinarith

def operationWordBound (q bound : Nat) : Nat := 4*(q+1)+2*bound+12

theorem rowOp_encoded_bound (operation : RowOp q) (bound : Nat)
    (bounded : OperationBound bound operation) :
    (Encoding.rawRowOp.encode (RawRowOp.ofRowOp operation)).length ≤ operationWordBound q bound := by
  cases operation with
  | swap first second =>
    have a := ((show first.val.size ≤ first.val from Nat.size_le.mpr Nat.lt_two_pow_self)).trans (Nat.le_of_lt first.isLt)
    have b := ((show second.val.size ≤ second.val from Nat.size_le.mpr Nat.lt_two_pow_self)).trans (Nat.le_of_lt second.isLt)
    simp [RawRowOp.ofRowOp,Encoding.rawRowOp_swap,Encoding.natural_length,
      Encoding.rational_length,List.length_append,operationWordBound]
    omega
  | scale row factor =>
    have a := ((show row.val.size ≤ row.val from Nat.size_le.mpr Nat.lt_two_pow_self)).trans (Nat.le_of_lt row.isLt)
    change rationalBits factor ≤ bound at bounded
    simp only [RawRowOp.ofRowOp,Encoding.rawRowOp_scale,Encoding.natural_length,
      Encoding.rational_length,List.length_append,operationWordBound]
    norm_num
    dsimp only [rationalBits] at bounded
    omega
  | add target source factor =>
    have a := ((show target.val.size ≤ target.val from Nat.size_le.mpr Nat.lt_two_pow_self)).trans (Nat.le_of_lt target.isLt)
    have b := ((show source.val.size ≤ source.val from Nat.size_le.mpr Nat.lt_two_pow_self)).trans (Nat.le_of_lt source.isLt)
    change rationalBits factor ≤ bound at bounded
    simp only [RawRowOp.ofRowOp,Encoding.rawRowOp_add,Encoding.natural_length,show Nat.size 2=2 from by decide,
      Encoding.rational_length,List.length_append,operationWordBound]
    norm_num
    dsimp only [rationalBits] at bounded
    omega

theorem operations_encoded_bound (operations : List (RowOp q)) (bound : Nat)
    (bounded : ∀ operation ∈ operations,OperationBound bound operation) :
    (Encoding.gaussianOpsRev (operations.map RawRowOp.ofRowOp)).length ≤
      operations.length*(2*operationWordBound q bound+1) := by
  have result := encoded_sequence_length_le (Encoding.framed Encoding.rawRowOp)
    (operations.map RawRowOp.ofRowOp) (2*operationWordBound q bound+1) (by
      intro raw member
      obtain ⟨operation,present,rfl⟩ := List.mem_map.mp member
      rw [Encoding.framed_length]
      have h := rowOp_encoded_bound operation bound (bounded operation present)
      omega)
  simpa only [Encoding.gaussianOpsRev,List.length_map] using result

theorem actual_partial_pivot_encoded_bound (original : Augmented q ℤ)
    (permutation : Fin q → Fin q) (state : GaussianState q) (pivot : Fin q) (rows : List (Fin q))
    (invariant : BasisInvariant original permutation pivot.val state.system)
    (ok : state.ok=true) (nonzero : state.system.coeff pivot pivot ≠ 0)
    (M : Nat) (bounded : ∀ i c,(original i c).natAbs ≤ M) :
    (Encoding.rationalMatrix.encode (augmentedMatrix (RationalSystem.eliminateRows pivot rows
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system)).length ≤
      40*(q+1)^2*(intermediateBound q M+1) :=
  augmentedMatrix_encoded_bound _ _
    (actual_partial_pivot_bound original permutation state pivot rows invariant ok nonzero M bounded)

end Counting.GaussianBits
