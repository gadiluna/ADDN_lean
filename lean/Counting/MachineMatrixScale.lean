import Counting.StackMatrixScaleInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.MatrixScale

def matrixScaleProgram : Program := StackMachine.Compiler.compile complete.program

/-- The physical operation reads the selected row from the encoded matrix,
scales every rational entry, and writes that row back. The bound includes
both matrix traversals and all parsing, arithmetic, framing and tape cleanup. -/
theorem matrixScale_clean (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    ∃ time output, time≤(20*150000000038^2)*((inputWord factor rows index.val).length+1)^8 ∧
      HaltsAt matrixScaleProgram (inputWord factor rows index.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts factor rows index
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord factor rows index.val).length
    change 20*(size+33+steps+4)^2≤(20*150000000038^2)*(size+1)^8
    have linear := Nat.le_self_pow (by decide : 4≠0) (size+1)
    have base : size+33+steps+4≤150000000038*(size+1)^4 := by
      change steps≤150000000000*(size+1)^4 at bounded
      omega
    calc
      _≤20*(150000000038*(size+1)^4)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
