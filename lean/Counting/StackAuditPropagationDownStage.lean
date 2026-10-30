import Counting.StackAuditPropagationDownBounds
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def downStageRoles : Fin 40 ↪ Fin 44 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 44=>r.val) equal)⟩
abbrev downStage : Routine 42 := relocate downLoop downStageRoles

def downStageStore (store : Store 42) (vista : Executable.Vista) (rounds : Nat) (weights : Array Nat) : Store 42 :=
  Function.update (Function.update (Function.update store 39 []) 22 []) 35
    ((Encoding.array Encoding.natural).encode (Executable.propagateDown vista rounds weights))

theorem downStage_executes (store : Store 42) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 44,i.val<17 → i≠1 → store i=[])
    (empty : ∀ i∈([18,19,20,21,23,24,25,26,30,31,32,33,37,38] : List (Fin 44)),store i=[])
    (vista : Executable.Vista) (weights : Array Nat) (sized : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (nodeCount : store 36=List.replicate vista.nodes.size true)
    (rounds : Nat) (level : store 22=rounds.bits) (counter : store 39=List.replicate rounds true)
    (depth : rounds ≤ vista.nodes.size) :
    ∃ time ≤ rounds*(downUniform vista (store 17).length
        (5*(((Encoding.array Encoding.natural).encode weights).length+1)^3)+2)+1,
      Executes downStage store time (downStageStore store vista rounds weights) := by
  let localStore : Store 38 := store ∘ downStageRoles
  have localWork (i : Fin 40) (small : i.val<17) (different : i≠1) : localStore i=[] := by
    apply work (downStageRoles i) small
    intro same;apply different
    exact Fin.ext (congrArg (fun j:Fin 44=>j.val) same)
  obtain ⟨time,bounded,body⟩ := downLoop_executes localStore accepted tail status localWork
    (empty 18 (by simp)) (empty 19 (by simp)) (empty 20 (by simp)) (empty 21 (by simp))
    (empty 23 (by simp)) (empty 24 (by simp)) (empty 25 (by simp)) (empty 26 (by simp))
    (empty 30 (by simp)) (empty 31 (by simp)) (empty 32 (by simp)) (empty 33 (by simp))
    (empty 37 (by simp)) (empty 38 (by simp)) vista weights sized nodeInput table weightInput nodeCount
    rounds level (List.replicate rounds true) counter (by simp)
  have tableAt : localStore 17=store 17 := rfl
  rw [tableAt] at bounded
  refine ⟨time,bounded.trans (downLoopBudget_polynomial vista (store 17).length rounds weights sized depth),?_⟩
  apply relocate_executes_frame downLoop downStageRoles _ _ _ _ time rfl _ _ body
  · intro i;fin_cases i <;> simp [downStageStore,downLoopStore,localStore,downStageRoles]
  · intro i outside
    have n22 : i≠22 := by intro same;subst i;exact outside 22 rfl
    have n35 : i≠35 := by intro same;subst i;exact outside 35 rfl
    have n39 : i≠39 := by intro same;subst i;exact outside 39 rfl
    simp [downStageStore,n22,n35,n39]

end Counting.StackMachine.AuditPropagation
