import Counting.StackRowAxpyInput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RowAxpy

def rowAxpyProgram : Program := StackMachine.Compiler.compile complete.program

/-- Physical Gaussian row addition on canonical row inputs, charging the
scaling, the addition, all input/output movement, and tape cleanup. -/
theorem rowAxpy_pairs_clean (factor : Rat) (pairs : List (Rat×Rat)) :
    ∃ time output,
      time ≤ (20*(completeCost+40)^2)*
        ((inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))).length+1)^32 ∧
      HaltsAt rowAxpyProgram (inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+factor*pair.2))).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts factor pairs
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))).length
    change 20*(size+35+steps+4)^2 ≤ (20*(completeCost+40)^2)*(size+1)^32
    have linear : size+1 ≤ (size+1)^16 := Nat.le_self_pow (by decide) _
    have positive := Nat.one_le_pow' 16 size
    have base : size+35+steps+4 ≤ (completeCost+40)*(size+1)^16 := by
      change steps ≤ completeCost*(size+1)^16 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeCost+40)*(size+1)^16)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by rw [Nat.mul_pow,← Nat.pow_mul,← Nat.mul_assoc]
  · rw [stored] at tape
    exact tape

theorem rowAxpy_clean (factor : Rat) (target source : List Rat) (sameLength : target.length=source.length) :
    ∃ time output,
      time ≤ (20*(completeCost+40)^2)*((inputCodec.encode (factor,(target,source))).length+1)^32 ∧
      HaltsAt rowAxpyProgram (inputCodec.encode (factor,(target,source))) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) target source)).map bitSymbol) := by
  have mapped : (target.zip source).map (fun pair => pair.1+factor*pair.2) =
      List.zipWith (fun a b=>a+factor*b) target source := by
    rw [List.map_zip_eq_zipWith]
    rfl
  simpa only [List.map_fst_zip sameLength.le,List.map_snd_zip sameLength.ge,mapped] using
    rowAxpy_pairs_clean factor (target.zip source)

end Counting.Machine
