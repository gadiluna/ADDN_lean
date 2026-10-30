import Counting.MachineGaussianInputBounds
import Counting.GaussianSolverPolynomial

namespace Counting.Machine
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem GaussianBits
open StackMachine.GaussianBank

/-- A fixed concrete Turing program solves every canonical integral square
system in a polynomial of the actual binary input length, including failed
and zero-dimensional systems. The theorem does not assert recognition of
malformed encodings or construction of rectangular normal equations. -/
theorem gaussian_system_polynomial_clean {q : Nat} (system : RationalSystem q)
    (integral : ∀ row column,(augmented system row column).den=1) :
    ∃ time output,
      time ≤ solverPhysicalCoefficient*
        ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)^200 ∧
      HaltsAt gaussianProgram (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode ((StoredGaussian.solve? system).map List.ofFn)).map bitSymbol) := by
  let length := (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length
  obtain ⟨time,output,bounded,halted,tape⟩ := gaussian_system_clean system (2^length) integral
    (fun row column => (augmented_numerator_lt_input_power system row column).le)
  have polynomial := solverPhysical_polynomial q (intermediateBound q (2^length)) length
    (augmented_dimension_le_input system) (intermediateBound_input_le system)
  exact ⟨time,output,bounded.trans polynomial,halted,tape⟩

theorem gaussian_integral_polynomial_clean {q : Nat} (original : Augmented q ℤ) :
    ∃ time output,
      time ≤ solverPhysicalCoefficient*
        ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))).length+1)^200 ∧
      HaltsAt gaussianProgram (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((StoredGaussian.solve? (integralSystem original)).map List.ofFn)).map bitSymbol) := by
  apply gaussian_system_polynomial_clean
  intro row column
  cases column <;> simp [augmented,integralSystem]

end Counting.Machine
