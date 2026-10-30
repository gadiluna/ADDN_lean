import Counting.StackMatrixSwapInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.MatrixSwap

def matrixSwapProgram : Program := StackMachine.Compiler.compile complete.program

/-- The entire encoded matrix is traversed and updated on the physical
tape. Indices are internal bounded unary fields; malformed inputs are outside
this canonical-input interface. -/
theorem matrixSwap_clean (rows : List (List Rat)) (first second : Fin rows.length) :
    ∃ time output, time ≤ (20*513^2)*((inputWord rows first.val second.val).length+1)^2 ∧
      HaltsAt matrixSwapProgram (inputWord rows first.val second.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts rows first second
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord rows first.val second.val).length
    change 20*(size+8+steps+4)^2 ≤ (20*513^2)*(size+1)^2
    have base : size+8+steps+4 ≤ 513*(size+1) := by
      change steps ≤ 500*(size+1) at bounded
      omega
    calc
      _ ≤ 20*(513*(size+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
