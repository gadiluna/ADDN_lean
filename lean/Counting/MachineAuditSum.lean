import Counting.StackAuditSumComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.AuditSum

def auditSumProgram : Program := StackMachine.Compiler.compile complete.program

theorem auditSum_clean (values : List Nat) (candidate : Nat) :
    ∃ time output,
      time≤(20*4027^2)*((inputWord values candidate).length+1)^6 ∧
      HaltsAt auditSumProgram (inputWord values candidate) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ([accepts values candidate].map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts values candidate
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord values candidate).length
    have linear : size+1≤(size+1)^3 := Nat.le_self_pow (by decide) _
    have positive : 1≤(size+1)^3 := Nat.one_le_pow' 3 size
    have base : size+22+steps+4≤4027*(size+1)^3 := by
      change steps≤4000*(size+1)^3 at bounded
      omega
    calc
      _ ≤20*(4027*(size+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ =_ := by ring
  · rw [stored] at tape
    exact tape

theorem auditSum_converted_clean (values : Array Rat) (natural : Array Nat)
    (converted : Executable.positiveNaturals? values=some natural) (candidate : Nat) :
    ∃ time output,
      time≤(20*4027^2)*((inputWord natural.toList candidate).length+1)^6 ∧
      HaltsAt auditSumProgram (inputWord natural.toList candidate) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ([decide (natural.toList.sum=candidate)].map bitSymbol) := by
  simpa only [accepts_after_conversion values natural converted] using auditSum_clean natural.toList candidate

end Counting.Machine
