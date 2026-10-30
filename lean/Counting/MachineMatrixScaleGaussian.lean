import Counting.MachineMatrixScale
import Counting.StoredGaussianMatrixOperations

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem

theorem scale_augmentedMatrix_clean {q : Nat} (system : RationalSystem q) (row : Fin q) (factor : Rat) :
    ∃ time output,
      time≤(20*150000000038^2)*((StackMachine.MatrixScale.inputWord factor (augmentedMatrix system) row.val).length+1)^8 ∧
      Machine.HaltsAt Machine.matrixScaleProgram
        (StackMachine.MatrixScale.inputWord factor (augmentedMatrix system) row.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode (augmentedMatrix (materialize (system.applyRowOp (.scale row factor))))).map Machine.bitSymbol) := by
  simpa only [scale_augmentedMatrix,augmentedMatrix_getElem] using
    Machine.matrixScale_clean factor (augmentedMatrix system) ⟨row.val,by simp [row.isLt]⟩

end Counting.StoredGaussian
