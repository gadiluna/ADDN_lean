import Counting.StackAuditDescendantCheck
import Counting.StackRoutineRelocate

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def checkRoles : Fin 40 ↪ Fin 48 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r:Fin 48=>r.val) same)⟩

/-- Keep the canonical node array for the next outer-loop iteration; each
inner check receives a real copy and erases the consumed bare table. -/
def preservingCheck : Routine 46 := sequence (ofProgram (ListPrograms.copyProgram 45 46 17 0))
  (sequence (relocate checkAncestor checkRoles) (clear 17))

theorem preservingCheck_executes (store : Store 46) (vista : Executable.Vista)
    (weights : Array Nat) (last ancestor : Nat) (steps : List Bool)
    (source : store 46=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (query : store 33=Encoding.natural.encode ancestor)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps)
    (empty : ∀ r : Fin 48,r.val<40 → r≠29 → r≠32 → r≠33 → r≠34 → r≠38 → store r=[]) :
    ∃ time ≤ 19000000000*((store 46).length+(store 32).length+(store 33).length+
        steps.length+(ancestor+1).size+last.size+1)^6,
      Executes preservingCheck store time
        (Function.update store 35 [decide (Executable.descendantCountRange vista steps.length last ancestor
          0 vista.nodes.size ≤ weights[ancestor]?.getD 0)]) := by
  have a:=copy_executes 45 (46:Fin 48) 17 0 (by decide) (by decide) (by decide) store
    (empty 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [empty 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),List.append_nil] at a
  let copied:=Function.update store 17 (store 46)
  let localStore : Store 38:=copied ∘ checkRoles
  obtain ⟨time,bound,b⟩:=checkAncestor_executes localStore vista weights last ancestor steps
    (by simp [localStore,copied,checkRoles,source])
    (by simp [localStore,copied,checkRoles,weightsAt])
    (by simp [localStore,copied,checkRoles,query])
    (by simp [localStore,copied,checkRoles,lastAt])
    (by simp [localStore,copied,checkRoles,target])
    (by simp [localStore,copied,checkRoles,stepBudget])
    (by simp [localStore,copied,checkRoles,empty])
    (by simp [localStore,copied,checkRoles,empty])
    (by simp [localStore,copied,checkRoles,empty])
    (by simp [localStore,copied,checkRoles,empty])
    (by simp [localStore,copied,checkRoles,empty])
    (by simp [localStore,copied,checkRoles,empty]) (by
      intro r small different
      fin_cases r <;> simp_all [localStore,copied,checkRoles])
  let answer:=decide (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size ≤
    weights[ancestor]?.getD 0)
  let checked:=Function.update (Function.update copied 17 (Encoding.sequence Encoding.node vista.nodes.toList))
    35 [answer]
  have checking : Executes (relocate checkAncestor checkRoles) copied time checked := by
    apply relocate_executes_frame _ checkRoles copied checked localStore _ time rfl _ _ b
    · intro r;fin_cases r <;> simp [checked,localStore,checkRoles,answer]
    · intro r outside
      have n17 : r≠17 := by intro same;subst r;exact outside 17 rfl
      have n35 : r≠35 := by intro same;subst r;exact outside 35 rfl
      simp [checked,n17,n35]
  have c:=clear_executes (17:Fin 48) checked
  have table : checked 17=Encoding.sequence Encoding.node vista.nodes.toList := by simp [checked]
  rw [table] at c
  have final : Function.update checked 17 []=Function.update store 35 [answer] := by
    funext r
    by_cases r17:r=17 <;> by_cases r35:r=35 <;>
      simp [checked,copied,r17,r35,empty]
  rw [final] at c
  have bareBound : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ (store 46).length := by
    rw [source]
    change (Encoding.sequence Encoding.node vista.nodes.toList).length ≤
      (Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [List.length_append];omega
  have tableAt : (localStore 17).length=(store 46).length := by simp [localStore,copied,checkRoles]
  have weightsSame : (localStore 32).length=(store 32).length := by simp [localStore,copied,checkRoles]
  have querySame : (localStore 33).length=(store 33).length := by simp [localStore,copied,checkRoles]
  rw [tableAt,weightsSame,querySame] at bound
  let K:=(store 46).length+(store 32).length+(store 33).length+
    steps.length+(ancestor+1).size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  have tableBound : (store 46).length ≤ K := by dsimp only [K];omega
  refine ⟨_,?_,a.sequence (checking.sequence c)⟩
  change 5*(store 46).length+2+1+(time+1+
    ((Encoding.sequence Encoding.node vista.nodes.toList).length+1)) ≤ 19000000000*K^6
  change time ≤ 18000000000*K^6 at bound
  omega

end Counting.StackMachine.AuditDescendant
