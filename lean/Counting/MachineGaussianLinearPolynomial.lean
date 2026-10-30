import Counting.MachineGaussianLinear
import Counting.GaussianLinearPolynomial
import Counting.GaussianAnchorDomain

namespace Counting.Machine
open StackMachine.GaussianCalls GaussianNormalMatrix
set_option maxRecDepth 20000
set_option exponentiation.threshold 4000

/-- A polynomial bound for the actual integral rectangular solver,
including normal-system construction and the original-equation checks. -/
theorem gaussianLinear_polynomial_clean (width : Nat) (equations : List Executable.Equation)
    (sized : Executable.RowsSized width equations)
    (coeffIntegral : ∀ r i,(Executable.rowMatrix width equations r i).den=1)
    (rhsIntegral : ∀ r,(Executable.rowRhs equations r).den=1) :
    ∃ time output,
      time≤ linearPhysicalCoefficient*
        ((StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)).length+1)^3000 ∧
      HaltsAt gaussianLinearProgram (StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((Executable.solveLinear? width equations).map Array.toList)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := gaussianLinear_clean width equations sized coeffIntegral rhsIntegral
  have cost := linearCost_polynomial width equations
    (GaussianSolveLinear.normal_integral width equations coeffIntegral rhsIntegral)
  let length := (StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)).length
  have positive := Nat.one_le_pow' 1500 length
  have linear := Nat.le_self_pow (by decide:1500≠0) (length+1)
  change linearCost width equations≤ linearPolynomialCoefficient*(length+1)^1500 at cost
  have base : length+58+linearCost width equations≤ (linearPolynomialCoefficient+59)*(length+1)^1500 := by
    generalize (length+1)^1500=P at *
    nlinarith only [cost,positive,linear]
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  calc
    _≤ 20*((linearPolynomialCoefficient+59)*(length+1)^1500)^2 :=
      Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _=linearPhysicalCoefficient*(length+1)^3000 := by
      have power : ((length+1)^1500)^2=(length+1)^3000 := (pow_mul (length+1) 1500 2).symm
      rw [mul_pow,power]
      exact (Nat.mul_assoc _ _ _).symm

/-- Every actual anchor system satisfies the integral and width premises;
the public solver's result is computed without additional mathematical
assumptions on that system. The supplied tape is the explicit internal
matrix encoding, not a free construction of anchor rows from a DAG. -/
theorem gaussianAnchor_polynomial_clean (vista : Executable.Vista) (anchor leaders : Nat) :
    let width := (Executable.levelNodes vista anchor).length
    let rows := Executable.anchorRows vista anchor leaders
    ∃ time output,
      time≤ linearPhysicalCoefficient*
        ((StackMachine.GaussianNormal.inputWord width (equationMatrix width rows)).length+1)^3000 ∧
      HaltsAt gaussianLinearProgram (StackMachine.GaussianNormal.inputWord width (equationMatrix width rows)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((Executable.solveLinear? width rows).map Array.toList)).map bitSymbol) := by
  dsimp only
  obtain ⟨coeff,rhs⟩ := Executable.anchorRows_integral vista anchor leaders (Executable.levelNodes vista anchor).length
  exact gaussianLinear_polynomial_clean _ _ (Executable.anchorRows_sized vista anchor leaders) coeff rhs

end Counting.Machine
