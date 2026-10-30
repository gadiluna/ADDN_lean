import Counting.MachineAuditComplete
import Counting.CountingSizeEncoding
import Counting.StackAuditCompleteEncoding

namespace Counting.Machine
open Executable StackMachine.AuditComplete

/-- Substitute the physical shared-DAG size bound into the uniform complete
audit machine bound. The coefficient and degree are independent of the
population, network, labels, and binary candidate/round parameters. -/
theorem audit_physical_polynomial : ∃ coefficient degree,
    ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool)
      (t : Nat) (observer : V) (vista : Vista)
      (_ : vista.valid=true) (_ : (vista.node vista.bottom).level=t)
      (_ : decodeNode vista t vista.bottom=Counting.history G leader t observer)
      (leaders candidate last M : Nat) (_ : ∀ r,0<r → r≤t → arcMass G r≤M),
      let n:=Fintype.card V
      let K:=(t+1)*n
      let B:=t+K+M.size+n+1
      ∃ time output,
        time≤coefficient*(K*(8*B+9+n*(4*B+2))+2*leaders.size+2*candidate.size+2*last.size+6)^degree ∧
        HaltsAt auditProgram (StackMachine.AuditPrefix.inputWord vista leaders candidate last) time output ∧
        output.tape.denotes=Turing.Tape.mk₁ ((witnessWord (audit? vista leaders candidate last)).map bitSymbol) := by
  obtain ⟨coefficient,degree,run⟩:=audit_polynomial
  refine ⟨coefficient,degree,?_⟩
  intro V inst G leader t observer vista valid depth physical leaders candidate last M mass
  dsimp only
  obtain ⟨time,output,bound,halted,tape⟩:=run vista leaders candidate last
  have code:=Encoding.physical_vista_encoding_length G leader t observer vista valid depth physical M mass
  dsimp only at code
  have inputBound : (StackMachine.AuditPrefix.inputWord vista leaders candidate last).length+1≤
      (t+1)*Fintype.card V*(8*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+9+
        Fintype.card V*(4*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+2))+
          2*leaders.size+2*candidate.size+2*last.size+6 := by
    rw [StackMachine.AuditPrefix.inputWord_length]
    omega
  exact ⟨time,output,bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputBound degree)),halted,tape⟩

end Counting.Machine
