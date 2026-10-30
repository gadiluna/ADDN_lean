import Counting.MachineMatrixAxpy
import Counting.StoredGaussianMatrixOperations

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

theorem add_augmentedMatrix_clean {q : Nat} (system : RationalSystem q) (target source : Fin q) (factor : Rat) :
    ∃ time output,
      time ≤ (20*(StackMachine.MatrixAxpy.completeCost+45)^2)*
        ((StackMachine.MatrixAxpy.inputWord factor (augmentedMatrix system) target.val source.val).length+1)^32 ∧
      Machine.HaltsAt Machine.matrixAxpyProgram
        (StackMachine.MatrixAxpy.inputWord factor (augmentedMatrix system) target.val source.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode (augmentedMatrix (materialize (system.applyRowOp (.add target source factor))))).map Machine.bitSymbol) := by
  simpa only [add_augmentedMatrix,augmentedMatrix_getElem] using
    Machine.matrixAxpy_clean factor (augmentedMatrix system)
      ⟨target.val,by simp [target.isLt]⟩ ⟨source.val,by simp [source.isLt]⟩ (by simp)

end Counting.StoredGaussian
