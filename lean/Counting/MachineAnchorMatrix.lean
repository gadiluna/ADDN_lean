import Counting.StackAnchorMatrix
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.AnchorMatrix

/-- A finite one-tape program constructing the actual anchor system. -/
def anchorMatrixProgram : Program := StackMachine.Compiler.compile complete.program

theorem anchorMatrix_clean (anchor leaders : Nat) (vista : Executable.Vista) :
    ∃ time output,
      time ≤ (20*(7000000053)^2)*((inputWord anchor leaders vista).length+1)^12 ∧
      HaltsAt anchorMatrixProgram (inputWord anchor leaders vista) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord anchor leaders vista).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts anchor leaders vista
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord anchor leaders vista).length
    change 20*(size+48+steps+4)^2 ≤ (20*(7000000053)^2)*(size+1)^12
    have linear : size+1 ≤ (size+1)^6 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^6 := Nat.one_le_pow' _ _
    have base : size+48+steps+4 ≤ 7000000053*(size+1)^6 := by
      change steps ≤ 7000000000*(size+1)^6 at bounded
      omega
    calc
      _ ≤ 20*(7000000053*(size+1)^6)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
