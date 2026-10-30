import Counting.StackAuditPositive

namespace Counting.Machine
open StackMachine.AuditPositive

def auditPositiveProgram : Program := StackMachine.Compiler.compile routine.program

/-- The physical machine checks every returned rational for integral and
strictly positive value, and faithfully propagates a failed solver result.
This is the initial conversion in `auditSuffix?`; MachineAuditComplete
combines it with the subsequent checks. -/
theorem auditPositive_clean (values : Option (Array Rat)) :
    ∃ time output,
      time≤(20*400035^2)*((inputWord values).length+1)^6 ∧
      HaltsAt auditPositiveProgram (inputWord values) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord values).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := routine_halts values
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord values).length
    have linear : size+1≤(size+1)^3 := Nat.le_self_pow (by decide) _
    have positive : 1≤(size+1)^3 := Nat.one_le_pow' 3 size
    have base : size+30+steps+4≤400035*(size+1)^3 := by
      change steps≤400000*(size+1)^3 at bounded
      omega
    calc
      _ ≤20*(400035*(size+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ =_ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
