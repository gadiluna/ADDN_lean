import Counting.StackAuditAscendPositive
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.AuditAscend
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def stepParent : Routine 30 := sequence (DagValidation.emptyFlag 24 26)
  (branchRoutine 26 (skip 30) positiveStep)

theorem stepParent_executes (store : Store 30) (vista : Executable.Vista) (code : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=code.bits)
    (empty : ∀ r : Fin 32,r.val≤28 → r≠17 → r≠24 → r≠25 → store r=[]) :
    ∃ time ≤ 5000000*((store 17).length+code.size+1)^4,
      Executes stepParent store time (Function.update store 24 (nextCode vista code).bits) := by
  have nil_iff : code.bits=[] ↔ code=0 := by
    constructor
    · intro same
      have values:=congrArg Encoding.value same
      simpa only [Encoding.value_bits,Encoding.value] using values
    · rintro rfl;rfl
  have a:=DagValidation.emptyFlag_executes (24:Fin 32) 26 store
  let flagged:=Function.update store 26 [decide (code=0)]
  have flagging : Executes (DagValidation.emptyFlag (24:Fin 32) 26) store
      (DagValidation.emptyFlagCost code.bits) flagged := by
    simpa only [current,empty 26 (by decide) (by decide) (by decide) (by decide),nil_iff,flagged] using a
  have restored : Function.update flagged 26 []=store := by
    simp only [flagged,Function.update_idem]
    rw [←empty 26 (by decide) (by decide) (by decide) (by decide),Function.update_eq_self]
  have flagBound : DagValidation.emptyFlagCost code.bits≤3 := by
    unfold DagValidation.emptyFlagCost;split <;> omega
  have one : 1≤((store 17).length+code.size+1)^4 := Nat.one_le_pow _ _ (by omega)
  by_cases zero : code=0
  · have b:=branch_executes_true (26:Fin 32) (skip 30) positiveStep flagged store [] 0
      (by simp [flagged,zero]) (by rw [restored];exact skip_executes store)
    have final : Function.update store 24 (nextCode vista code).bits=store := by
      rw [nextCode,if_pos zero]
      have currentZero : store 24=[] := by simpa [zero] using current
      change Function.update store 24 []=store
      rw [←currentZero,Function.update_eq_self]
    rw [final]
    exact ⟨_,by omega,flagging.sequence b⟩
  · obtain ⟨time,bound,b⟩:=positiveStep_executes store vista code source current zero empty
    have branch:=branch_executes_false (26:Fin 32) (skip 30) positiveStep flagged
      (Function.update store 24 (nextCode vista code).bits) [] time
      (by simp [flagged,zero]) (by rw [restored];exact b)
    exact ⟨_,by omega,flagging.sequence branch⟩

end Counting.StackMachine.AuditAscend

