import Counting.StackRationalToNat
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RationalArithmetic

def rationalToNatProgram : Program := StackMachine.Compiler.compile numeratorToNatRoutine.program

theorem rationalToNat_computesCleanIn : Complexity.ComputesCleanIn rationalToNatProgram
    (fun input => Encoding.natural.encode (numeratorNatural input)) (Complexity.polynomial (20*69^2) 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn numeratorToNat_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+14+50*(input.length+1)^1+4)^2 ≤ (20*69^2)*(input.length+1)^2
  simp only [pow_one]
  have base : input.length+14+50*(input.length+1)+4 ≤ 69*(input.length+1) := by omega
  calc
    _ ≤ 20*(69*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem rationalToNat_rational_clean (value : Rat) :
    ∃ time output,
      time ≤ (20*69^2)*((Encoding.rational.encode value).length+1)^2 ∧
      HaltsAt rationalToNatProgram (Encoding.rational.encode value) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode value.num.toNat).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalToNat_computesCleanIn (Encoding.rational.encode value)
  refine ⟨time,output,bounded,halted,?_⟩
  dsimp only at tape
  rw [numeratorNatural_rational] at tape
  exact tape

end Counting.Machine
