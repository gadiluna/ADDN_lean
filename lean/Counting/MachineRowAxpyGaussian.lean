import Counting.MachineRowAxpy
import Counting.MachineRowScaleGaussian

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem

def augmentedPairs {q : Nat} (system : RationalSystem q) (target source : Fin q) : List (Rat×Rat) :=
  List.ofFn (fun i => (system.coeff target i,system.coeff source i))++[(system.rhs target,system.rhs source)]

@[simp] theorem augmentedPairs_first {q : Nat} (system : RationalSystem q) (target source : Fin q) :
    (augmentedPairs system target source).map Prod.fst = augmentedRow system target := by
  simp [augmentedPairs,augmentedRow,List.map_ofFn,Function.comp_def]

@[simp] theorem augmentedPairs_second {q : Nat} (system : RationalSystem q) (target source : Fin q) :
    (augmentedPairs system target source).map Prod.snd = augmentedRow system source := by
  simp [augmentedPairs,augmentedRow,List.map_ofFn,Function.comp_def]

theorem add_augmentedRow {q : Nat} (system : RationalSystem q) (target source : Fin q) (factor : Rat) :
    augmentedRow (materialize (system.applyRowOp (.add target source factor))) target =
      (augmentedPairs system target source).map (fun pair => pair.1+factor*pair.2) := by
  simp [augmentedRow,augmentedPairs,applyRowOp,RowOp.transform,List.map_ofFn,Function.comp_def]

theorem add_other_augmentedRow {q : Nat} (system : RationalSystem q) (target source other : Fin q)
    (different : other≠target) (factor : Rat) :
    augmentedRow (materialize (system.applyRowOp (.add target source factor))) other = augmentedRow system other := by
  simp [augmentedRow,applyRowOp,RowOp.transform,different]

/-- Bit-step simulation of the selected augmented row of the actual Gaussian
add operation, used by the complete solver in MachineGaussianPolynomial. -/
theorem add_augmentedRow_clean {q : Nat} (system : RationalSystem q) (target source : Fin q) (factor : Rat) :
    ∃ time output,
      time ≤ (20*(StackMachine.RowAxpy.completeCost+40)^2)*
        ((StackMachine.RowAxpy.inputCodec.encode (factor,(augmentedRow system target,augmentedRow system source))).length+1)^32 ∧
      Machine.HaltsAt Machine.rowAxpyProgram
        (StackMachine.RowAxpy.inputCodec.encode (factor,(augmentedRow system target,augmentedRow system source))) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rationalRow.encode (augmentedRow (materialize (system.applyRowOp (.add target source factor))) target)).map Machine.bitSymbol) := by
  simpa only [augmentedPairs_first,augmentedPairs_second,← add_augmentedRow] using
    Machine.rowAxpy_pairs_clean factor (augmentedPairs system target source)

end Counting.StoredGaussian
