import Counting.StackAuditPrefixCountClassify
import Counting.StackRoutineMove

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

abbrev mergeFlag (source target : Fin 52) : Routine 50 :=
  sequence (move 49 source target 4) (ofProgram (combineFlagsProgram 50 target))

theorem mergeFlag_executes (source target : Fin 52) (distinct : source≠target)
    (scratchSource : source≠4) (scratchTarget : target≠4) (store : Store 50)
    (e4 : store 4=[]) (selected accepted : Bool) (tail : List Bool)
    (sourceAt : store source=[selected]) (targetAt : store target=accepted::tail) :
    Executes (mergeFlag source target) store 14
      (Function.update (Function.update store source []) target ((accepted && selected)::tail)) := by
  have a:=move_executes 49 source target 4 distinct scratchSource scratchTarget store e4
  rw [sourceAt,targetAt] at a
  let moved:=Function.update (Function.update store target (selected::accepted::tail)) source []
  have b:=combineFlags_executes 50 target moved accepted selected tail
    (by simp [moved,Ne.symm distinct])
  have final : Function.update moved target ((accepted && selected)::tail)=
      Function.update (Function.update store source []) target ((accepted && selected)::tail) := by
    funext r
    by_cases a:r=source <;> by_cases b:r=target <;> simp_all [moved]
  rw [final] at b
  exact a.sequence b

def childClassifyRoles : Fin 36 ↪ Fin 52 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r:Fin 52=>r.val) same)⟩

abbrev childFlags : Routine 50 := sequence (relocate (countClassify .child) childClassifyRoles)
  (sequence (mergeFlag 31 42) (mergeFlag 33 43))

def childFlagsResult (store : Store 50) (present unique : Bool) (tailExists tailUnique : List Bool)
    (amount : Nat) : Store 50 :=
  Function.update (Function.update store 42 ((present && decide (0<amount))::tailExists))
    43 ((unique && decide (amount=1))::tailUnique)

/-- One candidate parent's child scan updates both accumulated predicates:
at least one child and exactly one child. The actual child tally is bounded
by, and computed from, the explicitly stored DAG nodes. -/
theorem childFlags_executes (store : Store 50) (vista : Executable.Vista)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (level parent : Nat) (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits)
    (present unique : Bool) (tailExists tailUnique : List Bool)
    (existsAt : store 42=present::tailExists) (uniqueAt : store 43=unique::tailUnique) :
    ∃ time ≤ 22000*((store 17).length+level.size+parent.size+1)^5,
      Executes childFlags store time
        (childFlagsResult store present unique tailExists tailUnique
          (countRange vista .child level parent 0 vista.nodes.size)) := by
  let localStore:Store 34:=store ∘ childClassifyRoles
  have localWork (r:Fin 36) (small:r.val<17) (different:r≠1) : localStore r=[] := by
    apply work (childClassifyRoles r) small
    intro same;apply different;exact Fin.ext (congrArg (fun r:Fin 52=>r.val) same)
  obtain ⟨time,bound,run⟩:=countClassify_executes .child vista localStore accepted tail status localWork
    e18 e19 e28 e29 e31 e33 e34 e35 suffix input nodeCount level parent levelAt parentAt
  let amount:=countRange vista .child level parent 0 vista.nodes.size
  let counted:=Function.update (Function.update store 31 [decide (0<amount)]) 33 [decide (amount=1)]
  have a:Executes (relocate (countClassify .child) childClassifyRoles) store time counted := by
    apply relocate_executes_frame (countClassify .child) childClassifyRoles store counted localStore _ time rfl _ _ run
    · intro r;fin_cases r <;> simp [counted,localStore,childClassifyRoles,amount]
    · intro r outside
      have n31:r≠31 := by intro same;subst r;exact outside 31 rfl
      have n33:r≠33 := by intro same;subst r;exact outside 33 rfl
      simp [counted,n31,n33]
  have b:=mergeFlag_executes 31 42 (by decide) (by decide) (by decide) counted
    (by simp [counted,work]) (decide (0<amount)) present tailExists
    (by simp [counted]) (by simp [counted,existsAt])
  let first:=Function.update (Function.update counted 31 []) 42 ((present && decide (0<amount))::tailExists)
  have c:=mergeFlag_executes 33 43 (by decide) (by decide) (by decide) first
    (by simp [first,counted,work]) (decide (amount=1)) unique tailUnique
    (by simp [first,counted]) (by simp [first,counted,uniqueAt])
  have final : Function.update (Function.update first 33 []) 43 ((unique && decide (amount=1))::tailUnique)=
      childFlagsResult store present unique tailExists tailUnique amount := by
    funext r
    by_cases a:r=31 <;> by_cases b:r=33 <;> by_cases c:r=42 <;> by_cases d:r=43 <;>
      simp [childFlagsResult,first,counted,a,b,c,d,e31,e33]
  rw [final] at c
  have tableSame : (localStore 17).length=(store 17).length := rfl
  rw [tableSame] at bound
  have positive : 1≤((store 17).length+level.size+parent.size+1)^5 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

end Counting.StackMachine.AuditPrefix
