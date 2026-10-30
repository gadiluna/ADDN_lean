import Counting.StackDagParentRemapPositive

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def remapParentCode (mapping : List Nat) (code : Nat) : Nat :=
  if code=0 then 0 else (mapping[code-1]?.getD 0)+1

abbrev remapParent : Routine 18 := sequence (DagValidation.emptyFlag 1 19)
  (branchRoutine 19 (skip 18) remapParentPositive)

/-- Exact total remapping of the optional-parent encoding. Empty bits mean
None; all positive codes, including missing references, use binary lookup. -/
theorem remapParent_executes (store : Store 18) (mapping : List Nat) (code : Nat)
    (source : store 0=(Encoding.list Encoding.natural).encode mapping)
    (query : store 1=code.bits)
    (empty : ∀ r : Fin 20,r≠0 → r≠1 → store r=[]) :
    ∃ time ≤ 2100*((store 0).length+code.size+1)^3,
      Executes remapParent store time (Function.update store 2 (remapParentCode mapping code).bits) := by
  have nil_iff : code.bits=[] ↔ code=0 := by
    constructor
    · intro same
      have values:=congrArg Encoding.value same
      simpa only [Encoding.value_bits,Encoding.value] using values
    · rintro rfl;rfl
  have flagging:=DagValidation.emptyFlag_executes (1:Fin 20) 19 store
  let flagged:=Function.update store 19 [decide (code=0)]
  have flagAs : Executes (DagValidation.emptyFlag (1:Fin 20) 19) store
      (DagValidation.emptyFlagCost code.bits) flagged := by
    simpa only [query,empty 19 (by decide) (by decide),nil_iff,flagged] using flagging
  have restored : Function.update flagged 19 []=store := by
    simp only [flagged,Function.update_idem]
    rw [←empty 19 (by decide) (by decide),Function.update_eq_self]
  have flagBound : DagValidation.emptyFlagCost code.bits ≤ 3 := by
    unfold DagValidation.emptyFlagCost
    split <;> omega
  have one : 1 ≤ ((store 0).length+code.size+1)^3 := Nat.one_le_pow _ _ (by omega)
  by_cases zero : code=0
  · have branch:=branch_executes_true (19:Fin 20) (skip 18) remapParentPositive flagged store [] 0
      (by simp [flagged,zero]) (by rw [restored];exact skip_executes store)
    have result : Function.update store 2 (remapParentCode mapping code).bits=store := by
      rw [remapParentCode,if_pos zero]
      change Function.update store 2 []=store
      rw [←empty 2 (by decide) (by decide),Function.update_eq_self]
    rw [result]
    exact ⟨_,by omega,flagAs.sequence branch⟩
  · obtain ⟨time,bound,positive⟩:=remapParentPositive_executes store mapping code source query empty
    have branch:=branch_executes_false (19:Fin 20) (skip 18) remapParentPositive flagged
      (Function.update store 2 ((mapping[code-1]?.getD 0)+1).bits) [] time
      (by simp [flagged,zero]) (by rw [restored];exact positive)
    simpa only [remapParentCode,if_neg zero] using
      (show ∃ time ≤ 2100*((store 0).length+code.size+1)^3,
        Executes remapParent store time
          (Function.update store 2 ((mapping[code-1]?.getD 0)+1).bits) from
        ⟨_,by omega,flagAs.sequence branch⟩)

/-- The output is precisely the optional-parent field of referenceMap. -/
theorem remapParentCode_referenceMap (mapping : Array Nat) (node : Executable.Node) :
    remapParentCode mapping.toList (node.parent.map (·+1) |>.getD 0)=
      ((Executable.referenceMap mapping node).parent.map (·+1) |>.getD 0) := by
  cases parent : node.parent with
  | none => simp [remapParentCode,Executable.referenceMap,parent]
  | some index => simp [remapParentCode,Executable.referenceMap,parent]

end Counting.StackMachine.DagUpdate
