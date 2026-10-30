import Counting.StackProtocolAuditPolynomial

namespace Counting.Machine
open StackMachine.ProtocolAudit

def scheduledAuditProgram : Program := StackMachine.Compiler.compile complete.program

/-- The scheduled candidate choice and complete audit are one fixed physical
machine. All parsing, binary arithmetic, branch control, witness erasure and
register cleanup are included in its uniform polynomial bit cost. -/
theorem scheduledAudit_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders round : Nat),
      ∃ time output,
        time≤ coefficient*((inputWord vista leaders round).length+1)^degree ∧
        HaltsAt scheduledAuditProgram (inputWord vista leaders round) time output ∧
        output.tape.denotes=Turing.Tape.mk₁ ((outputWord (answer vista leaders round)).map bitSymbol) := by
  obtain ⟨coefficient,degree,polynomial⟩:=complete_polynomial
  refine ⟨20*(coefficient+75)^2,(degree+1)*2,?_⟩
  intro vista leaders round
  obtain ⟨steps,bound,finish,ran,halted,stored⟩:=polynomial vista leaders round
  have stackHalt : StackMachine.HaltsAt complete.program (inputWord vista leaders round) steps finish := ⟨ran,halted⟩
  obtain ⟨time,output,timeBound,executed,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size:=(inputWord vista leaders round).length+1
    have positive:1≤ size := by dsimp only [size];omega
    have linear:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
    have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
    have raised:=bound.trans (Nat.mul_le_mul_left coefficient
      (Nat.pow_le_pow_right positive (show degree≤ degree+1 by omega)))
    have base:(inputWord vista leaders round).length+70+steps+4≤
        (coefficient+75)*size^(degree+1) := by
      rw [Nat.add_mul]
      dsimp only [size] at linear one raised ⊢
      omega
    calc
      _≤ 20*((coefficient+75)*size^(degree+1))^2:=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _= _:=by rw [mul_pow,←pow_mul];simp only [Nat.mul_assoc,size]
  · have value:finish.store 1=outputWord (answer vista leaders round) := by rw [stored];rfl
    rw [value] at tape
    exact tape

end Counting.Machine
