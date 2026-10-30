import Counting.StackRowScaleInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RowScale

/-- The physical one-tape implementation of coefficient-wise rational row scaling. -/
def rowScaleProgram : Program := StackMachine.Compiler.compile complete.program

/-- Correctness and bit-step cost on the actual row codec. This statement is
restricted to canonical encoded inputs; it makes no claim about malformed rows. -/
theorem rowScale_clean (factor : Rat) (row : List Rat) :
    ∃ time output,
      time ≤ (20*(3000000000+30+5)^2)*((inputCodec.encode (factor,row)).length+1)^8 ∧
      HaltsAt rowScaleProgram (inputCodec.encode (factor,row)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rationalRow.encode (row.map (factor*·))).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts factor row
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputCodec.encode (factor,row)).length
    change 20*(size+30+steps+4)^2 ≤ (20*(3000000000+30+5)^2)*(size+1)^8
    have linear : size+1 ≤ (size+1)^4 := by
      have cube := Nat.one_le_pow' 3 size
      have product := Nat.mul_le_mul_left (size+1) cube
      nlinarith
    have positive := Nat.one_le_pow' 4 size
    have base : size+30+steps+4 ≤ (3000000000+30+5)*(size+1)^4 := by
      change steps ≤ 3000000000*(size+1)^4 at bounded
      omega
    calc
      _ ≤ 20*((3000000000+30+5)*(size+1)^4)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
