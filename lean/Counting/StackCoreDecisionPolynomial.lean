import Counting.StackCoreDecisionComplete

namespace Counting.StackMachine.CoreDecision
open Routine ProtocolDecision
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem rawBudget_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders : Nat),vista.valid=true →
      rawBudget vista leaders≤ coefficient*((inputWord vista leaders).length+1)^degree := by
  obtain ⟨coefficient,degree,polynomial⟩:=CoreAudit.completeBudget_polynomial
  refine ⟨coefficient*4^degree+4000000,degree+5,?_⟩
  intro vista leaders valid
  let round:=(vista.node vista.bottom).level
  let size:=(inputWord vista leaders).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have inputLength:(inputWord vista leaders).length=2*leaders.size+(Encoding.vista.encode vista).length+1 := by
    simp [inputWord,Encoding.natural_length];omega
  have nodeBound:=Encoding.nodeBits_le_vista vista vista.bottom (RealizabilityVerifier.bottom_inside vista valid)
  have depthBound:round.size≤ (Encoding.vista.encode vista).length := by
    unfold Encoding.nodeBits at nodeBound
    dsimp only [round]
    omega
  have vistaBound:(Encoding.vista.encode vista).length+1≤ size := by dsimp only [size];omega
  have summaryBound:(ProtocolVista.outputWord vista).length+1≤ 3*size := by
    simp only [ProtocolVista.outputWord,List.length_append,Encoding.natural_length,List.length_singleton]
    dsimp only [round,size] at depthBound ⊢
    omega
  have labels:leaders.size+round.size+1≤ 2*size := by dsimp only [size];omega
  have auditInput:(ProtocolAudit.inputWord vista leaders round).length+1≤ 4*size := by
    rw [ProtocolAudit.inputWord_length]
    dsimp only [size]
    omega
  have auditBound:CoreAudit.completeBudget vista leaders round≤
      coefficient*(4*size)^degree := (polynomial vista leaders round).trans
        (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left auditInput degree))
  have auditRaised:CoreAudit.completeBudget vista leaders round≤
      (coefficient*4^degree)*size^(degree+5) := by
    calc
      _≤ coefficient*(4*size)^degree:=auditBound
      _= (coefficient*4^degree)*size^degree:=by rw [mul_pow];ring
      _≤ (coefficient*4^degree)*size^(degree+5):=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by omega))
  have vistaCost:3000000*((Encoding.vista.encode vista).length+1)^5≤ 3000000*size^(degree+5):=
    Nat.mul_le_mul_left 3000000 ((Nat.pow_le_pow_left vistaBound 5).trans
      (Nat.pow_le_pow_right positive (by omega)))
  have linear:size≤ size^(degree+5):=Nat.le_self_pow (by omega) _
  have one:1≤ size^(degree+5):=Nat.one_le_pow _ _ positive
  unfold rawBudget normalBudget
  change 20*size+3000000*((Encoding.vista.encode vista).length+1)^5+
    20*((ProtocolVista.outputWord vista).length+1)+
    (30*((ProtocolAudit.inputWord vista leaders round).length+1)+CoreAudit.completeBudget vista leaders round+1)+
    40*(leaders.size+round.size+1)+13≤ (coefficient*4^degree+4000000)*size^(degree+5)
  rw [Nat.add_mul]
  omega

theorem completeBudget_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders : Nat),vista.valid=true →
      completeBudget vista leaders≤ coefficient*((inputWord vista leaders).length+1)^degree := by
  obtain ⟨coefficient,degree,polynomial⟩:=rawBudget_polynomial
  refine ⟨81*coefficient+324,degree+1,?_⟩
  intro vista leaders valid
  let size:=(inputWord vista leaders).length+1
  have positive:1≤ size := by dsimp only [size];omega
  have linear:size≤ size^(degree+1):=Nat.le_self_pow (by omega) _
  have one:1≤ size^(degree+1):=Nat.one_le_pow _ _ positive
  have raised:rawBudget vista leaders≤ coefficient*size^(degree+1):=
    (polynomial vista leaders valid).trans
      (Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_right positive (by omega)))
  unfold completeBudget
  rw [Nat.add_mul,Nat.mul_assoc]
  dsimp only [size] at linear one raised ⊢
  omega

/-- Uniform polynomial execution of the complete original scheduledPlan
from its genuine local input. This includes reading the round and all-leader
predicate, finite control, the full audit and clean output. -/
theorem complete_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders : Nat),vista.valid=true → 0<leaders →
      ∃ time≤ coefficient*((inputWord vista leaders).length+1)^degree,
        Executes complete (inputStore 78 (inputWord vista leaders)) time
          (outputStore 78 (outputWord (Executable.coreScheduledPlan leaders vista).eval)) := by
  obtain ⟨coefficient,degree,polynomial⟩:=completeBudget_polynomial
  refine ⟨coefficient,degree,?_⟩
  intro vista leaders valid positive
  obtain ⟨time,bounded,run⟩:=complete_executes vista leaders valid positive
  exact ⟨time,bounded.trans (polynomial vista leaders valid),run⟩

end Counting.StackMachine.CoreDecision
