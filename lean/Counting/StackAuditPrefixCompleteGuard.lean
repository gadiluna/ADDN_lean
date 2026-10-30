import Counting.StackAuditPrefixCompleteActive

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev resumeActive : Routine 50 := sequence (pushBit 1 true) completeActive
abbrev completeRaw : Routine 50 := sequence opening
  (branchRoutine 1 resumeActive (pushBit 1 false))

/-- Canonical binary inputs, including malformed vistas and arbitrary round
labels, produce the literal `auditPrefix?` answer. Failed opening guards never
allocate an unbounded unary round counter. -/
theorem completeRaw_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time output,time ≤ 61000000000*((inputWord vista leaders candidate last).length+1)^7 ∧
      Executes completeRaw (inputStore 50 (inputWord vista leaders candidate last)) time output ∧
      output 1=Encoding.optionalNatural.encode (Executable.auditPrefix? vista leaders candidate last) := by
  obtain ⟨openingTime,openingBound,a⟩:=opening_executes vista leaders candidate last
  let L:=(inputWord vista leaders candidate last).length+1
  have positive : 1≤L := by dsimp only [L];omega
  have one : 1≤L^7:=Nat.one_le_pow _ _ positive
  have openingLimit : openingTime≤230000000*L^7:=openingBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide)))
  cases acceptedEq:openingAccepted vista leaders candidate last with
  | false=>
    rw [acceptedEq] at a
    let opened:=openingFile vista leaders candidate last false
    let consumed:=Function.update opened 1 []
    have status : opened 1=[false] := by simp [opened,openingFile]
    have rejected:=pushBit_executes (1:Fin 52) false consumed
    have restored : Function.update consumed 1 (false::consumed 1)=opened := by
      simp only [consumed,Function.update_self,Function.update_idem]
      rw [←status,Function.update_eq_self]
    rw [restored] at rejected
    have branch:=branch_executes_false (1:Fin 52) resumeActive (pushBit 1 false)
      opened opened [] 1 status rejected
    refine ⟨_,opened,?_,a.sequence branch,?_⟩
    · change openingTime+1+(1+1)≤61000000000*L^7
      omega
    · rw [auditPrefix_eq_counts,acceptedEq]
      exact status
  | true=>
    rw [acceptedEq] at a
    obtain ⟨valid,_,_,_,depth,fit⟩:=openingAccepted_bounds vista leaders candidate last acceptedEq
    obtain ⟨activeTime,output,activeBound,b,result⟩:=completeActive_executes vista leaders candidate last
      valid depth (by omega)
    let opened:=openingFile vista leaders candidate last true
    let consumed:=Function.update opened 1 []
    have status : opened 1=[true] := by simp [opened,openingFile]
    have pushed:=pushBit_executes (1:Fin 52) true consumed
    have restored : Function.update consumed 1 (true::consumed 1)=opened := by
      simp only [consumed,Function.update_self,Function.update_idem]
      rw [←status,Function.update_eq_self]
    rw [restored] at pushed
    have branch:=branch_executes_true (1:Fin 52) resumeActive (pushBit 1 false)
      opened output [] _ status (pushed.sequence b)
    refine ⟨_,output,?_,a.sequence branch,?_⟩
    · change activeTime≤60000000000*L^7 at activeBound
      change openingTime+1+(1+(1+1+activeTime))≤61000000000*L^7
      omega
    · rw [auditPrefix_eq_counts,acceptedEq]
      exact result

end Counting.StackMachine.AuditPrefix
