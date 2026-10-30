import Counting.StackRowDotInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RowDot

/-- The physical one-tape implementation of rational dot product. -/
def rowDotProgram : Program := StackMachine.Compiler.compile complete.program

/-- Correctness and bit-step cost on the actual row codec. This statement is
restricted to canonical encoded inputs; it makes no claim about malformed rows. -/
theorem rowDot_pairs_clean (pairs : List (Rat×Rat)) :
    ∃ time output,
      time ≤ (20*(100000000000000+34+5)^2)*((inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)).length+1)^8 ∧
      HaltsAt rowDotProgram (inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum)).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts pairs
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)).length
    change 20*(size+34+steps+4)^2 ≤ (20*(100000000000000+34+5)^2)*(size+1)^8
    have linear : size+1 ≤ (size+1)^4 := by
      have cube := Nat.one_le_pow' 3 size
      have product := Nat.mul_le_mul_left (size+1) cube
      nlinarith
    have positive := Nat.one_le_pow' 4 size
    have base : size+34+steps+4 ≤ (100000000000000+34+5)*(size+1)^4 := by
      change steps ≤ 100000000000000*(size+1)^4 at bounded
      omega
    calc
      _ ≤ 20*((100000000000000+34+5)*(size+1)^4)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

/-- The same physical transducer on any two rows of equal length. -/
theorem rowDot_clean (left right : List Rat) (sameLength : left.length=right.length) :
    ∃ time output,
      time ≤ (20*(100000000000000+34+5)^2)*((inputCodec.encode (left,right)).length+1)^8 ∧
      HaltsAt rowDotProgram (inputCodec.encode (left,right)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rational.encode ((List.zipWith (·*·) left right).sum)).map bitSymbol) := by
  have mapped : (left.zip right).map (fun pair => pair.1*pair.2) = List.zipWith (·*·) left right := by
    rw [List.map_zip_eq_zipWith]
    rfl
  simpa only [List.map_fst_zip sameLength.le,List.map_snd_zip sameLength.ge,mapped] using
    rowDot_pairs_clean (left.zip right)

end Counting.Machine
