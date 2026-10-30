import Counting.StackAuditPropagationPolynomial

namespace Counting.Machine
open StackMachine.AuditPropagation

def auditPropagationProgram : Program := StackMachine.Compiler.compile completePropagation.program

/-- A finite physical Turing machine for the actual executable backward
propagation. The whole tape contains only the canonical result on termination. -/
theorem auditPropagation_clean (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time output,
      time ≤ (20*(propagationCoefficient+47)^2)*
        ((propagationInputWord anchor vista values).length+1)^64 ∧
      HaltsAt auditPropagationProgram (propagationInputWord anchor vista values) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((propagationOutputWord anchor vista values).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := completePropagation_halts anchor vista values fits
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (propagationInputWord anchor vista values).length
    have linear : size+1 ≤ (size+1)^32 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^32 := Nat.one_le_pow' 32 size
    have base : size+42+steps+4 ≤ (propagationCoefficient+47)*(size+1)^32 := by
      change steps ≤ propagationCoefficient*(size+1)^32 at bounded
      simp only [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((propagationCoefficient+47)*(size+1)^32)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ =_ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
