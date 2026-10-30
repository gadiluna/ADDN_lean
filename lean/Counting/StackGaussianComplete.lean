import Counting.StackGaussianOutput
import Counting.StackGaussianActualBounds

namespace Counting.StackMachine.GaussianBank
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem GaussianBits

def solverBudget (q bits : Nat) : Nat := generatorBudget q bits+1+
  (5*q+3+2000*(matrixBudget q bits+q+2)^2+5)

theorem complete_halts_integral {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) :
    ∃ steps output,steps ≤ solverBudget q (intermediateBound q M) ∧
      HaltsAt complete.program (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))) steps output ∧
      output.store 1=(Encoding.optional Encoding.rationalRow).encode
        ((StoredGaussian.solve? (integralSystem original)).map List.ofFn) := by
  obtain ⟨generateTime,generateBound,generated⟩ := generateInput_integral original M bounded
  obtain ⟨formatTime,formatBound,formatted⟩ := formatOutput_executes (StoredGaussian.runGaussian (integralSystem original))
  have invariant := runGaussian_safe original M bounded
  have matrix := augmentedMatrix_encoded_bound _ _ invariant.current
  rw [←StoredGaussian.runGaussian_eq] at matrix
  change _ ≤ matrixBudget q (intermediateBound q M) at matrix
  have finalBound : rhsCost (StoredGaussian.runGaussian (integralSystem original)).system ≤
      5*q+3+2000*(matrixBudget q (intermediateBound q M)+q+2)^2 := by
    dsimp only [rhsCost]
    gcongr
  obtain ⟨last,ran,halted,stored⟩ := generated.sequence formatted
  refine ⟨generateTime+1+formatTime,last,?_,⟨?_,halted⟩,?_⟩
  · dsimp only [solverBudget]
    omega
  · have initialEqual : initial complete.program
        (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original)))=
        ⟨0,inputFile (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))) [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [inputFile]
    rw [initialEqual]
    exact ran
  · rw [stored,outputStore_output,encodedSolution_solve]

end Counting.StackMachine.GaussianBank
