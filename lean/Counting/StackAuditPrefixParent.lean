import Counting.StackAuditPropagationSelect

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def parentSelectRoles : Fin 32 ↪ Fin 52 :=
  ⟨fun r=>if r=30 then 41 else if r=31 then 35 else ⟨r.val,by omega⟩,by decide⟩

abbrev selectParent : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 36 18 4))
  (sequence (relocate AuditPropagation.selectedLevel parentSelectRoles) (clear 18))

/-- Read a candidate parent's actual level with a copied physical index.
The persistent parent index and child-level query remain untouched. -/
theorem selectParent_executes (store : Store 50) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (level : Nat) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (indexAt : (store 36).length=index.val) (levelAt : store 41=level.bits) :
    ∃ time ≤ 9000*((store 17).length+level.size+1)^4,
      Executes selectParent store time (Function.update store 35
        (decide ((vista.node index.val).level=level)::store 35)) := by
  have a:=copy_executes 49 (36:Fin 52) 18 4 (by decide) (by decide) (by decide) store
    (work 4 (by decide) (by decide))
  rw [e18,List.append_nil] at a
  let copied:=Function.update store 18 (store 36)
  let localStore:Store 30:=copied ∘ parentSelectRoles
  let selected:Fin vista.nodes.toList.length:=⟨index.val,by simp⟩
  have localWork (r:Fin 32) (small:r.val<17) (different:r≠1) : localStore r=[] := by
    have n30:r≠30 := by intro same;subst r;norm_num at small
    have n31:r≠31 := by intro same;subst r;norm_num at small
    have n1:(⟨r.val,by omega⟩:Fin 52)≠1 := by
      intro equal;apply different;exact Fin.ext (congrArg (fun q:Fin 52=>q.val) equal)
    have n18:(⟨r.val,by omega⟩:Fin 52)≠18 := by
      intro equal;have:=congrArg (fun q:Fin 52=>q.val) equal;dsimp at this;omega
    simp only [localStore,Function.comp_apply,parentSelectRoles,Function.Embedding.coeFn_mk,
      if_neg n30,if_neg n31,copied,Function.update_of_ne n18]
    exact work _ small n1
  obtain ⟨time,bound,b⟩:=AuditPropagation.selectedLevel_executes localStore accepted tail
    (by simp [localStore,copied,parentSelectRoles,status]) localWork
    (by simp [localStore,copied,parentSelectRoles,e19]) vista.nodes.toList selected suffix
    (by simp [localStore,copied,parentSelectRoles,source])
    (by simpa [localStore,copied,parentSelectRoles,selected] using indexAt)
    level (by simp [localStore,copied,parentSelectRoles,levelAt])
  have nodeSame : vista.nodes.toList[selected]=vista.node index.val := by
    simp [selected,Executable.Vista.node]
  rw [nodeSame] at b
  let checked:=Function.update copied 35 (decide ((vista.node index.val).level=level)::store 35)
  have wide : Executes (relocate AuditPropagation.selectedLevel parentSelectRoles) copied time checked := by
    apply relocate_executes_frame AuditPropagation.selectedLevel parentSelectRoles copied checked localStore _ time rfl _ _ b
    · intro r;fin_cases r <;> simp [checked,localStore,copied,parentSelectRoles]
    · intro r outside
      have n35:r≠35 := by intro equal;subst r;exact outside 31 rfl
      simp [checked,n35]
  have c:=clear_executes (18:Fin 52) checked
  have indexLength : (checked 18).length=index.val := by simpa [checked,copied] using indexAt
  rw [indexLength] at c
  have final : Function.update checked 18 []=Function.update store 35
      (decide ((vista.node index.val).level=level)::store 35) := by
    funext r
    by_cases a:r=18 <;> by_cases b:r=35 <;> simp [checked,copied,a,b,e18]
  rw [final] at c
  have tableSame : (localStore 17).length=(store 17).length := by simp [localStore,copied,parentSelectRoles]
  rw [tableSame] at bound
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  have countBound : vista.nodes.size≤(store 17).length := by
    rw [source,List.length_append];simp only [Array.length_toList] at nodes;omega
  let S:=(store 17).length+level.size+1
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  refine ⟨_,?_,a.sequence (wide.sequence c)⟩
  rw [indexAt]
  have:=index.isLt
  dsimp only [S] at linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
