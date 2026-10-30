import Counting.StackGaussianComplete
import Counting.StackCompilerComplete
import Counting.GaussianIntermediateActual

namespace Counting.Machine
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
open StackMachine.GaussianBank GaussianBits

def gaussianProgram : Program := StackMachine.Compiler.compile complete.program

/-- Concrete Gaussian solving on every canonical integral square system.
All traversal, arithmetic, transcript generation, output formatting and
physical tape cleanup are charged. No nonsingularity premise is needed. -/
theorem gaussian_integral_clean {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) :
    ∃ time output,
      time ≤ 20*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))).length+
        55+solverBudget q (intermediateBound q M))^2 ∧
      HaltsAt gaussianProgram (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((StoredGaussian.solve? (integralSystem original)).map List.ofFn)).map bitSymbol) := by
  obtain ⟨steps,last,boundedSteps,halted,stored⟩ := complete_halts_integral original M bounded
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · change 20*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))).length+
        51+steps+4)^2 ≤ _
    exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
  · rw [stored] at tape
    exact tape

theorem gaussian_system_clean {q : Nat} (system : RationalSystem q) (M : Nat)
    (integral : ∀ row column,(augmented system row column).den=1)
    (bounded : ∀ row column,(augmented system row column).num.natAbs ≤ M) :
    ∃ time output,
      time ≤ 20*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+
        55+solverBudget q (intermediateBound q M))^2 ∧
      HaltsAt gaussianProgram (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode ((StoredGaussian.solve? system).map List.ofFn)).map bitSymbol) := by
  have result := gaussian_integral_clean (integerEntries system) M bounded
  simpa only [integralSystem_integerEntries system integral] using result

end Counting.Machine
