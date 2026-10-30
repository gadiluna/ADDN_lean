import Counting.MachineMatrixSwap
import Counting.MachineRowScaleGaussian

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- Dense materialization of the full augmented matrix, including rhs. -/
def augmentedMatrix {q : Nat} (system : RationalSystem q) : List (List Rat) :=
  List.ofFn (augmentedRow system)

@[simp] theorem augmentedMatrix_length {q : Nat} (system : RationalSystem q) :
    (augmentedMatrix system).length=q := by simp [augmentedMatrix]

@[simp] theorem augmentedMatrix_getElem {q : Nat} (system : RationalSystem q) (row : Fin q) :
    (augmentedMatrix system)[row.val]'(by simp [row.isLt])=augmentedRow system row := by
  simp [augmentedMatrix]

theorem swap_augmentedMatrix {q : Nat} (system : RationalSystem q) (first second : Fin q) :
    augmentedMatrix (materialize (system.applyRowOp (.swap first second)))=
      ((augmentedMatrix system).set first.val (augmentedRow system second)).set second.val (augmentedRow system first) := by
  apply List.ext_getElem (by simp)
  intro index leftBound _rightBound
  have inside : index<q := by simpa using leftBound
  by_cases same : first=second
  · subst second
    by_cases selected : index=first.val
    · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,selected]
    · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,selected,Ne.symm selected]
  · have different : first.val≠second.val := fun h => same (Fin.ext h)
    by_cases atFirst : index=first.val
    · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,atFirst,Ne.symm different]
    · by_cases atSecond : index=second.val
      · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,atSecond,Ne.symm different]
      · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,atFirst,atSecond,
          Ne.symm atFirst,Ne.symm atSecond]

theorem swap_augmentedMatrix_clean {q : Nat} (system : RationalSystem q) (first second : Fin q) :
    ∃ time output,
      time ≤ (20*513^2)*((StackMachine.MatrixSwap.inputWord (augmentedMatrix system) first.val second.val).length+1)^2 ∧
      Machine.HaltsAt Machine.matrixSwapProgram
        (StackMachine.MatrixSwap.inputWord (augmentedMatrix system) first.val second.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode (augmentedMatrix (materialize (system.applyRowOp (.swap first second))))).map Machine.bitSymbol) := by
  have checked := Machine.matrixSwap_clean (augmentedMatrix system)
    ⟨first.val,by simp [first.isLt]⟩ ⟨second.val,by simp [second.isLt]⟩
  simpa only [swap_augmentedMatrix,augmentedMatrix_getElem] using checked

end Counting.StoredGaussian
