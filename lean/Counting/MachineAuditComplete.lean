import Counting.StackAuditCompletePolynomial

namespace Counting.Machine
open StackMachine.AuditComplete

def auditProgram : Program := StackMachine.Compiler.compile complete.program

/-- A single fixed finite-alphabet Turing machine computes the actual
five-step executable audit and leaves its entire tape clean. No validity,
population, anchor, or unary-loop-budget assumption is supplied externally. -/
theorem audit_clean (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time output,
      time≤ 20*((StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+66+
        completeBudget vista leaders candidate last)^2 ∧
      HaltsAt auditProgram (StackMachine.AuditPrefix.inputWord vista leaders candidate last) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((witnessWord (Executable.audit? vista leaders candidate last)).map bitSymbol) := by
  obtain ⟨steps,finish,bound,halted,stored⟩:=complete_halts vista leaders candidate last
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change (StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+62+steps+4≤ _
    omega
  · rw [stored] at tape
    exact tape

/-- Polynomial physical bit cost of the complete audit, with one uniform
coefficient and degree for all canonically encoded inputs, including invalid
vistas and binary parameters that fail the opening guards. -/
theorem audit_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders candidate last : Nat),
      ∃ time output,
        time≤ coefficient*((StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+1)^degree ∧
        HaltsAt auditProgram (StackMachine.AuditPrefix.inputWord vista leaders candidate last) time output ∧
        output.tape.denotes=Turing.Tape.mk₁ ((witnessWord (Executable.audit? vista leaders candidate last)).map bitSymbol) := by
  obtain ⟨coefficient,degree,polynomial⟩:=complete_polynomial
  refine ⟨20*(coefficient+67)^2,(degree+1)*2,?_⟩
  intro vista leaders candidate last
  obtain ⟨steps,bound,finish,ran,halted,stored⟩:=polynomial vista leaders candidate last
  have stackHalt : StackMachine.HaltsAt complete.program
      (StackMachine.AuditPrefix.inputWord vista leaders candidate last) steps finish := ⟨ran,halted⟩
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+1
    have positive:1≤ size := by dsimp only [size];omega
    have linear:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
    have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
    have raised:=bound.trans (Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_right positive (show degree≤ degree+1 by omega)))
    have base:(StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+62+steps+4≤
        (coefficient+67)*size^(degree+1) := by
      rw [Nat.add_mul]
      dsimp only [size] at linear one raised ⊢
      omega
    calc
      _≤ 20*((coefficient+67)*size^(degree+1))^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc,size]
  · have value:finish.store 1=witnessWord (Executable.audit? vista leaders candidate last) := by rw [stored];rfl
    rw [value] at tape
    exact tape

end Counting.Machine
