import Counting.StackAuditCandidate

namespace Counting.Machine
open StackMachine.AuditCandidate

def auditCandidateProgram : Program := StackMachine.Compiler.compile complete.program

/-- Physical realization of the audit's optional-solution, positive integral
conversion and candidate-sum tests. Propagation and its checks are separate. -/
theorem auditCandidate_clean (values : Option (Array Rat)) (candidate : Nat) :
    ∃ time output,
      time ≤ (20*500039^2)*((inputWord values candidate).length+1)^6 ∧
      HaltsAt auditCandidateProgram (inputWord values candidate) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord values candidate).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts values candidate
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord values candidate).length
    have linear : size+1 ≤ (size+1)^3 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^3 := Nat.one_le_pow' 3 size
    have base : size+34+steps+4 ≤ 500039*(size+1)^3 := by
      change steps ≤ 500000*(size+1)^3 at bounded
      omega
    calc
      _ ≤ 20*(500039*(size+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ =_ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
