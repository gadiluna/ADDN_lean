import Counting.StackMatrixAxpyInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.MatrixAxpy

def matrixAxpyProgram : Program := StackMachine.Compiler.compile complete.program

/-- Complete physical Gaussian row addition, including two reads from the
original matrix, arithmetic on the coefficient streams, and replacement of
the target row. Equal indices are permitted, with their total semantics. -/
theorem matrixAxpy_clean (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    ∃ time output,
      time ≤ (20*(completeCost+45)^2)*((inputWord factor rows target.val source.val).length+1)^32 ∧
      HaltsAt matrixAxpyProgram (inputWord factor rows target.val source.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode
          (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts factor rows target source sameLength
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord factor rows target.val source.val).length
    change 20*(size+40+steps+4)^2 ≤ (20*(completeCost+45)^2)*(size+1)^32
    have linear := Nat.le_self_pow (by decide : 16≠0) (size+1)
    have positive := Nat.one_le_pow' 16 size
    have base : size+40+steps+4 ≤ (completeCost+45)*(size+1)^16 := by
      change steps ≤ completeCost*(size+1)^16 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _ ≤20*((completeCost+45)*(size+1)^16)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by rw [Nat.mul_pow,← Nat.pow_mul,← Nat.mul_assoc]
  · rw [stored] at tape
    exact tape

end Counting.Machine
