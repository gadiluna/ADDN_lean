import Counting.MachineAuditPrefix
import Counting.CountingSizeEncoding

namespace Counting.Machine
open Executable StackMachine.AuditPrefix

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Substitute the proved encoding size of an actual physical vista into
the complete prefix machine bound. Candidate and round arguments contribute
their binary lengths, including arguments rejected by the opening guard. -/
theorem auditPrefix_physical_clean (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (leaders candidate last M : Nat) (mass : ∀ r,0<r → r≤t → arcMass G r≤M) :
    let n:=Fintype.card V
    let K:=(t+1)*n
    let B:=t+K+M.size+n+1
    ∃ time output,
      time≤(20*(completeCoefficient+55)^2)*
        (K*(8*B+9+n*(4*B+2))+2*leaders.size+2*candidate.size+2*last.size+6)^14 ∧
      HaltsAt auditPrefixProgram (inputWord vista leaders candidate last) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.optionalNatural.encode (auditPrefix? vista leaders candidate last)).map bitSymbol) := by
  dsimp only
  obtain ⟨time,output,bound,halted,tape⟩:=auditPrefix_clean vista leaders candidate last
  have code:=Encoding.physical_vista_encoding_length G leader t observer vista valid depth physical M mass
  dsimp only at code
  have inputBound : (inputWord vista leaders candidate last).length+1≤
      (t+1)*Fintype.card V*(8*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+9+
        Fintype.card V*(4*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+2))+
          2*leaders.size+2*candidate.size+2*last.size+6 := by
    rw [inputWord_length]
    omega
  exact ⟨time,output,bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputBound 14)),halted,tape⟩

end Counting.Machine
