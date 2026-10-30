import Counting.StackProtocolScheduleComplete

namespace Counting.Machine
open StackMachine.ProtocolSchedule

def candidateScheduleProgram : Program := StackMachine.Compiler.compile complete.program

/-- The actual optimized candidate schedule is computed by a fixed physical
machine in quadratic bit time, with the entire tape clean on return. -/
theorem candidateSchedule_clean (leaders round : Nat) :
    ∃ time output,time≤ (20*4019^2)*((inputWord leaders round).length+1)^2 ∧
      HaltsAt candidateScheduleProgram (inputWord leaders round) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord (Executable.candidateAt leaders round)).map bitSymbol) := by
  obtain ⟨steps,finish,bound,halted,stored⟩:=complete_halts leaders round
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · have base:(inputWord leaders round).length+14+steps+4≤ 4019*((inputWord leaders round).length+1) := by omega
    calc
      _≤ 20*(4019*((inputWord leaders round).length+1))^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
