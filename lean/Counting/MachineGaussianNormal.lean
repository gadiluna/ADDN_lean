import Counting.StackGaussianNormalComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.GaussianNormal GaussianNormalMatrix

/-- A fixed physical transducer computing the augmented Gram system from
an explicit unary width and the canonical augmented equation matrix. -/
def gaussianNormalProgram : Program := StackMachine.Compiler.compile complete.program

/-- The headers, row/column loops, arithmetic, framing, and complete tape
cleanup are all executed. The input convention is the internal augmented
matrix codec, with its width represented explicitly in unary. -/
theorem gaussianNormal_clean (width : Nat) (equations : List Executable.Equation) :
    ∃ time output,
      time ≤ 20*(normalPolynomialCoefficient+56)^2*
        ((inputWord width (equationMatrix width equations)).length+1)^12 ∧
      HaltsAt gaussianNormalProgram (inputWord width (equationMatrix width equations)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts_polynomial width equations
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord width (equationMatrix width equations)).length
    change 20*(size+51+steps+4)^2≤20*(normalPolynomialCoefficient+56)^2*(size+1)^12
    have linear : size+1≤(size+1)^6 := Nat.le_self_pow (by decide : 6≠0) _
    have positive := Nat.one_le_pow' 6 size
    change steps≤ normalPolynomialCoefficient*(size+1)^6 at bounded
    have base : size+51+steps+4≤(normalPolynomialCoefficient+56)*(size+1)^6 := by nlinarith
    calc
      _≤20*((normalPolynomialCoefficient+56)*(size+1)^6)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
