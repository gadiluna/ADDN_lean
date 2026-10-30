import Counting.MachineRowScale
import Counting.StoredGaussian

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem

/-- All coefficients and the right-hand side are stored in the same row. -/
def augmentedRow {q : Nat} (system : RationalSystem q) (row : Fin q) : List Rat :=
  List.ofFn (system.coeff row)++[system.rhs row]

@[simp] theorem augmentedRow_length {q : Nat} (system : RationalSystem q) (row : Fin q) :
    (augmentedRow system row).length = q+1 := by simp [augmentedRow]

/-- The finite row transducer covers the right-hand side as well as every
coefficient in the scale operation used by StoredGaussian. -/
theorem scale_augmentedRow {q : Nat} (system : RationalSystem q) (row : Fin q) (factor : Rat) :
    augmentedRow (materialize (system.applyRowOp (.scale row factor))) row =
      (augmentedRow system row).map (factor*·) := by
  simp [augmentedRow,applyRowOp,RowOp.transform,List.map_ofFn,Function.comp_def]

theorem scale_other_augmentedRow {q : Nat} (system : RationalSystem q) (row other : Fin q)
    (different : other≠row) (factor : Rat) :
    augmentedRow (materialize (system.applyRowOp (.scale row factor))) other = augmentedRow system other := by
  simp [augmentedRow,applyRowOp,RowOp.transform,different]

/-- A physical bit-cost proof for one selected Gaussian scaling row. Fetching
and replacing that row inside the whole matrix are separate operations. -/
theorem scale_augmentedRow_clean {q : Nat} (system : RationalSystem q) (row : Fin q) (factor : Rat) :
    ∃ time output,
      time ≤ (20*(3000000000+30+5)^2)*
        ((StackMachine.RowScale.inputCodec.encode (factor,augmentedRow system row)).length+1)^8 ∧
      Machine.HaltsAt Machine.rowScaleProgram
        (StackMachine.RowScale.inputCodec.encode (factor,augmentedRow system row)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rationalRow.encode (augmentedRow (materialize (system.applyRowOp (.scale row factor))) row)).map Machine.bitSymbol) := by
  simpa only [scale_augmentedRow] using Machine.rowScale_clean factor (augmentedRow system row)

end Counting.StoredGaussian
