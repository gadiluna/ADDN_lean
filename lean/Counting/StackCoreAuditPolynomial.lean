import Counting.StackCoreAuditComplete

namespace Counting.StackMachine.CoreAudit
open Routine ProtocolAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The selected audit input cannot grow faster than the actually executed
binary scheduler. This bound does not expand a numeric round into unary. -/
theorem selected_input_bounded (vista : Executable.Vista) (leaders round candidate last : Nat)
    (chosen : CoreSchedule.candidate leaders round=some (candidate,last)) :
    (AuditPrefix.inputWord vista leaders candidate last).length+1≤
      4002*((inputWord vista leaders round).length+1) := by
  obtain ⟨time,bounded,run⟩:=CoreSchedule.complete_executes leaders round
  rw [chosen] at run
  have length:=AuditComplete.executed_output_length _ _ _ _ run
  change (true::selectedWord candidate last).length≤ (ProtocolSchedule.inputWord leaders round).length+time at length
  simp only [List.length_cons] at length
  have selected:=selectedWord_length candidate last
  have audit:=AuditPrefix.inputWord_length vista leaders candidate last
  have input:=inputWord_length vista leaders round
  have schedule:(ProtocolSchedule.inputWord leaders round).length=2*leaders.size+2*round.size+2 := by
    simp [ProtocolSchedule.inputWord,Encoding.natural_length];omega
  omega

theorem rawBudget_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders round : Nat),
      rawBudget vista leaders round≤ coefficient*((inputWord vista leaders round).length+1)^degree := by
  obtain ⟨coefficient,degree,polynomial⟩:=AuditComplete.completeCostBound_poly
  let factor:=500006+2*coefficient*4002^degree
  refine ⟨factor,degree+1,?_⟩
  intro vista leaders round
  let size:=(inputWord vista leaders round).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have raised:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
  have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
  have schedule:(ProtocolSchedule.inputWord leaders round).length+1≤ size := by
    simp only [size,inputWord,ProtocolSchedule.inputWord,List.length_append]
    omega
  cases chosen:CoreSchedule.candidate leaders round with
  | none =>
    simp only [rawBudget,chosen,afterScheduleBudget]
    change 40*size+4000*((ProtocolSchedule.inputWord leaders round).length+1)+2+2≤ factor*size^(degree+1)
    have factorLarge:500006≤ factor := by dsimp only [factor];omega
    have enlarge:=Nat.mul_le_mul_right (size^(degree+1)) factorLarge
    omega
  | some pair =>
    rcases pair with ⟨candidate,last⟩
    have inputLimit:=selected_input_bounded vista leaders round candidate last chosen
    have auditBound:AuditComplete.completeBudget vista leaders candidate last≤
        coefficient*(4002*size)^degree := by
      exact (AuditComplete.completeBudget_bounded vista leaders candidate last).trans
        ((polynomial _ (by omega)).trans (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left inputLimit degree)))
    have powers:size^degree≤ size^(degree+1):=Nat.pow_le_pow_right positive (by omega)
    have auditRaised:2*AuditComplete.completeBudget vista leaders candidate last≤
        (2*coefficient*4002^degree)*size^(degree+1) := by
      calc
        _≤ 2*(coefficient*(4002*size)^degree):=Nat.mul_le_mul_left 2 auditBound
        _= (2*coefficient*4002^degree)*size^degree := by rw [mul_pow];ring
        _≤ (2*coefficient*4002^degree)*size^(degree+1):=Nat.mul_le_mul_left _ powers
    simp only [rawBudget,chosen,afterScheduleBudget,selectedBudget]
    change 40*size+4000*((ProtocolSchedule.inputWord leaders round).length+1)+
      (100*((AuditPrefix.inputWord vista leaders candidate last).length+1)+
        2*AuditComplete.completeBudget vista leaders candidate last+5+1)+2≤ factor*size^(degree+1)
    dsimp only [factor]
    rw [Nat.add_mul]
    change (AuditPrefix.inputWord vista leaders candidate last).length+1≤ 4002*size at inputLimit
    omega

theorem completeBudget_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders round : Nat),
      completeBudget vista leaders round≤ coefficient*((inputWord vista leaders round).length+1)^degree := by
  obtain ⟨coefficient,degree,polynomial⟩:=rawBudget_polynomial
  refine ⟨73*coefficient+292,degree+1,?_⟩
  intro vista leaders round
  let size:=(inputWord vista leaders round).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have raised:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
  have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
  have rawRaised:rawBudget vista leaders round≤ coefficient*size^(degree+1):=
    (polynomial vista leaders round).trans
      (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_right positive (by omega)))
  unfold completeBudget
  rw [Nat.add_mul,Nat.mul_assoc]
  dsimp only [size] at raised one rawRaised ⊢
  omega

/-- Uniform polynomial stack cost of real scheduled candidate selection and
complete audit execution, including output conversion and all cleanup. -/
theorem complete_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders round : Nat),
      ∃ time≤ coefficient*((inputWord vista leaders round).length+1)^degree,
        Executes complete (inputStore 70 (inputWord vista leaders round)) time
          (outputStore 70 (outputWord (answer vista leaders round))) := by
  obtain ⟨coefficient,degree,polynomial⟩:=rawBudget_polynomial
  refine ⟨73*coefficient+292,degree+1,?_⟩
  intro vista leaders round
  obtain ⟨time,bounded,run⟩:=complete_executes vista leaders round
  let size:=(inputWord vista leaders round).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have raised:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
  have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
  have rawRaised:rawBudget vista leaders round≤ coefficient*size^(degree+1):=
    (polynomial vista leaders round).trans
      (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_right positive (by omega)))
  refine ⟨time,bounded.trans ?_,run⟩
  unfold completeBudget
  rw [Nat.add_mul,Nat.mul_assoc]
  dsimp only [size] at raised one rawRaised ⊢
  omega

end Counting.StackMachine.CoreAudit
