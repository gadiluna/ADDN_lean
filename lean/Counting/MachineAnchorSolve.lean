import Counting.StackAnchorSolve
import Counting.StackCompilerComplete

namespace Counting.Machine
set_option exponentiation.threshold 10000
set_option maxRecDepth 131072
open StackMachine.AnchorSolve

private theorem product_power (c s : Nat) : 20*(c*s^4500)^2=(20*c^2)*s^9000 := by
  rw [mul_pow,←pow_mul]
  simp only [Nat.mul_assoc]

def anchorSolveProgram : Program := StackMachine.Compiler.compile routine.program

theorem anchorSolve_clean (vista : Executable.Vista) (anchor leaders : Nat) :
    ∃ time output,
      time ≤ (20*(polynomialCoefficient+59)^2)*
        ((StackMachine.AnchorMatrix.inputWord anchor leaders vista).length+1)^9000 ∧
      HaltsAt anchorSolveProgram (StackMachine.AnchorMatrix.inputWord anchor leaders vista) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((resultWord vista anchor leaders).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := routine_halts vista anchor leaders
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (StackMachine.AnchorMatrix.inputWord anchor leaders vista).length+1
    have linear : size ≤ size^4500 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ size^4500 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
    have base : (StackMachine.AnchorMatrix.inputWord anchor leaders vista).length+54+steps+4 ≤
        (polynomialCoefficient+59)*size^4500 := by
      change steps ≤ polynomialCoefficient*size^4500 at bounded
      have sizeEq : (StackMachine.AnchorMatrix.inputWord anchor leaders vista).length+1=size := rfl
      rw [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((polynomialCoefficient+59)*size^4500)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := product_power _ _
  · rw [stored] at tape
    exact tape

end Counting.Machine
