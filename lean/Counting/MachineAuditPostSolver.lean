import Counting.StackAuditPostSolverPolynomial

namespace Counting.Machine
open StackMachine.AuditPostSolver

def auditPostSolverProgram : Program := StackMachine.Compiler.compile complete.program

/-- A concrete physical machine for conversion, candidate sum, propagation
and balance. Its optional weights are exactly the input to the remaining
descendant test, as specified by `auditSuffix_after_result`. -/
theorem auditPostSolver_clean (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat))
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time output,
      time ≤ (20*(completeCoefficient+59)^2)*((inputWord vista candidate anchor values).length+1)^102 ∧
      HaltsAt auditPostSolverProgram (inputWord vista candidate anchor values) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord vista candidate anchor values).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩:=complete_halts vista candidate anchor values fits valid
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(inputWord vista candidate anchor values).length
    have linear : size+1 ≤ (size+1)^51 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^51 := Nat.one_le_pow' 51 size
    have base : size+54+steps+4 ≤ (completeCoefficient+59)*(size+1)^51 := by
      change steps ≤ completeCoefficient*(size+1)^51 at bounded
      simp only [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeCoefficient+59)*(size+1)^51)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
