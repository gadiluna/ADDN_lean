import Counting.StackAuditPropagationSelect
import Counting.AuditDescendantSpec

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def levelRoles : Fin 32 ↪ Fin 40 :=
  ⟨fun r=>if r=30 then 34 else if r=31 then 35 else ⟨r.val,by omega⟩,by decide⟩

/-- Read the actual selected node's level, preserve the comparison target
and consume the supplied unary index after the physical lookup. -/
def levelTest : Routine 38 := sequence (pushBit 1 true)
  (sequence (relocate AuditPropagation.selectedLevel levelRoles)
    (sequence (clear 1) (clear 18)))

theorem levelTest_executes (store : Store 38) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (last : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (indexAt : (store 18).length=index.val) (target : store 34=last.bits)
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → r≠18 → r≠24 → r≠25 → store r=[]) :
    ∃ time ≤ 9000*((store 17).length+last.size+1)^4,
      Executes levelTest store time
        (Function.update (Function.update store 18 []) 35
          (decide ((vista.node index.val).level=last)::store 35)) := by
  have status:=pushBit_executes (1:Fin 40) true store
  rw [empty 1 (by decide) (by decide) (by decide) (by decide) (by decide)] at status
  let ready:=Function.update store 1 [true]
  let localStore : Store 30:=ready ∘ levelRoles
  let selected : Fin vista.nodes.toList.length:=⟨index.val,by simpa only [Array.length_toList] using index.isLt⟩
  have nodeSame : vista.nodes.toList[selected]=vista.node index.val := by
    change vista.nodes.toList[index.val]=vista.node index.val
    simp only [Executable.Vista.node,Array.getElem_toList,Array.getElem?_eq_getElem index.isLt,Option.getD_some]
  obtain ⟨time,bound,run⟩:=AuditPropagation.selectedLevel_executes localStore true []
    (by simp [localStore,ready,levelRoles]) (by
      intro r small different
      have r30 : r≠30 := by intro same;subst r;norm_num at small
      have r31 : r≠31 := by intro same;subst r;norm_num at small
      have r1 : (⟨r.val,by omega⟩ : Fin 40)≠1 := by
        intro same
        apply different
        exact Fin.ext (congrArg (fun q : Fin 40=>q.val) same)
      simp only [localStore,Function.comp_apply,levelRoles,Function.Embedding.coeFn_mk,
        if_neg r30,if_neg r31,ready,Function.update_of_ne r1]
      apply empty (⟨r.val,by omega⟩ : Fin 40) (by change r.val ≤ 28;omega)
      all_goals
        intro same
        have equal:=congrArg (fun q : Fin 40=>q.val) same
        dsimp at equal
        omega)
    (by simp [localStore,ready,levelRoles,empty]) vista.nodes.toList selected []
    (by simp [localStore,ready,levelRoles,source])
    (by simpa [localStore,ready,levelRoles,selected] using indexAt)
    last (by simp [localStore,ready,levelRoles,target])
  have actualNode : vista.nodes.toList[selected].level=(vista.node index.val).level := congrArg (·.level) nodeSame
  rw [actualNode] at run
  let checked:=Function.update ready 35 (decide ((vista.node index.val).level=last)::store 35)
  have relocated : Executes (relocate AuditPropagation.selectedLevel levelRoles) ready time checked := by
    apply relocate_executes_frame AuditPropagation.selectedLevel levelRoles ready checked localStore
      (Function.update localStore 31 (decide ((vista.node index.val).level=last)::localStore 31)) time rfl _ _ run
    · intro r
      fin_cases r <;> simp [checked,localStore,ready,levelRoles]
    · intro r outside
      have different : r≠35 := fun same=>outside 31 (by simpa [levelRoles] using same.symm)
      simp [checked,different]
  have clearStatus:=clear_executes (1:Fin 40) checked
  have statusAt : checked 1=[true] := by simp [checked,ready]
  rw [statusAt] at clearStatus
  let cleared:=Function.update checked 1 []
  have clearIndex:=clear_executes (18:Fin 40) cleared
  have counterLength : (cleared 18).length=index.val := by simpa [cleared,checked,ready] using indexAt
  rw [counterLength] at clearIndex
  have final : Function.update cleared 18 []=
      Function.update (Function.update store 18 []) 35
        (decide ((vista.node index.val).level=last)::store 35) := by
    funext r
    by_cases r1 : r=1 <;> by_cases r18 : r=18 <;> by_cases r35 : r=35 <;>
      simp [cleared,checked,ready,r1,r18,r35,empty]
  rw [final] at clearIndex
  refine ⟨_,?_,status.sequence (relocated.sequence (clearStatus.sequence clearIndex))⟩
  have tableLength : (localStore 17).length=(store 17).length := by simp [localStore,ready,levelRoles]
  rw [tableLength] at bound
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList,←source] at nodes
  let K:=(store 17).length+last.size+1
  have linear : K ≤ K^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^4:=Nat.one_le_pow _ _ (by dsimp only [K];omega)
  have indexBound : index.val ≤ K := by have:=index.isLt;dsimp only [K];omega
  change time ≤ 8000*K^4 at bound
  change 1+1+(time+1+((List.length [true]+1)+1+(index.val+1))) ≤ 9000*K^4
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.StackMachine.AuditDescendant
