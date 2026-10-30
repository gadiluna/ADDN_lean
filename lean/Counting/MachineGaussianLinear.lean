import Counting.StackGaussianLinearComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.GaussianCalls GaussianNormalMatrix

def gaussianLinearProgram : Program := StackMachine.Compiler.compile complete.program

/-- End-to-end physical semantics for the integral rectangular solver.
This structural budget includes every real subroutine; its polynomial
majorant is stated separately from this exact-interface theorem. -/
theorem gaussianLinear_clean (width : Nat) (equations : List Executable.Equation)
    (sized : Executable.RowsSized width equations)
    (coeffIntegral : ∀ r i,(Executable.rowMatrix width equations r i).den=1)
    (rhsIntegral : ∀ r,(Executable.rowRhs equations r).den=1) :
    ∃ time output,
      time≤20*((StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)).length+
        58+linearCost width equations)^2 ∧
      HaltsAt gaussianLinearProgram (StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((Executable.solveLinear? width equations).map Array.toList)).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts width equations sized coeffIntegral rhsIntegral
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · change 20*((StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)).length+54+steps+4)^2≤_
    exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2)
  · rw [stored] at tape
    exact tape

end Counting.Machine
