import Counting.StackAuditPrefixComplete

namespace Counting.Machine
open StackMachine.AuditPrefix

def auditPrefixProgram : Program := StackMachine.Compiler.compile complete.program

/-- A fixed finite-alphabet Turing machine computes the complete executable
audit prefix, including rejected and malformed vistas. Its input contains
only the three binary parameters and the shared DAG, and its tape is clean. -/
theorem auditPrefix_clean (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time output,
      time≤(20*(completeCoefficient+55)^2)*((inputWord vista leaders candidate last).length+1)^14 ∧
      HaltsAt auditPrefixProgram (inputWord vista leaders candidate last) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.optionalNatural.encode (Executable.auditPrefix? vista leaders candidate last)).map bitSymbol) := by
  obtain ⟨steps,finish,bound,halted,stored⟩:=complete_halts vista leaders candidate last
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(inputWord vista leaders candidate last).length
    have linear : size+1≤(size+1)^7:=Nat.le_self_pow (by decide) _
    have positive : 1≤(size+1)^7:=Nat.one_le_pow' 7 size
    have base : size+50+steps+4≤(completeCoefficient+55)*(size+1)^7 := by
      change steps≤completeCoefficient*(size+1)^7 at bound
      simp only [Nat.add_mul]
      omega
    calc
      _≤20*((completeCoefficient+55)*(size+1)^7)^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_:=by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
