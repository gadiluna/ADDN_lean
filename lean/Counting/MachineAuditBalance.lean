import Counting.StackAuditBalancePolynomial

namespace Counting.Machine
open StackMachine.AuditBalance

def auditBalanceProgram : Program := StackMachine.Compiler.compile completeBalance.program

/-- Physical computation of the literal audit balance checks, including
input parsing, bounded counters and whole-tape cleanup. -/
theorem auditBalance_clean (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    ∃ time output,
      time ≤ (20*(balanceCoefficient+53)^2)*
        ((balanceInputWord anchor vista weights).length+1)^34 ∧
      HaltsAt auditBalanceProgram (balanceInputWord anchor vista weights) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.boolean.encode (Executable.auditBalance vista weights anchor)).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩:=completeBalance_halts anchor vista weights fits valid length
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(balanceInputWord anchor vista weights).length
    have linear : size+1 ≤ (size+1)^17 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^17 := Nat.one_le_pow' 17 size
    have base : size+48+steps+4 ≤ (balanceCoefficient+53)*(size+1)^17 := by
      change steps ≤ balanceCoefficient*(size+1)^17 at bounded
      simp only [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((balanceCoefficient+53)*(size+1)^17)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
