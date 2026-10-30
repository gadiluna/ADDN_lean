import Counting.StackAuditPropagationUpdateCurrent
import Counting.StackAuditPropagationSelect

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def levelSelectRoles : Fin 32 ↪ Fin 40 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 40=>r.val) equal)⟩

abbrev levelChoice : Routine 38 := sequence (relocate selectedLevel levelSelectRoles)
  (branchRoutine 31 updateCurrent (skip 38))
abbrev levelItem : Routine 38 := sequence levelChoice (pushBit 18 true)

def levelChoiceWeights (vista : Executable.Vista) (r old : Nat) (weights : Array Nat) : Array Nat :=
  if (vista.node old).level=r then
    weights.setIfInBounds old (RealizabilityVerifier.childCount vista weights r old) else weights

/-- Test the physical node's level, then perform exactly the selected
backward update. All queries are binary and the traversal index is bounded
by the actual number of DAG nodes. -/
theorem levelChoice_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 40,i.val<17 → i≠1 → store i=[])
    (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e31 : store 31=[]) (e33 : store 33=[])
    (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (r : Nat) (old : Fin vista.nodes.size)
    (level : store 22=(r+1).bits) (query : store 30=r.bits)
    (counter : store 18=List.replicate old.val true) :
    ∃ time ≤ 8000*((store 17).length+r.size+1)^4+
      20000*((store 34).length+(store 35).length+(r+1).size+old.val+2)^5+2,
      Executes levelChoice store time
        (Function.update store 35 ((Encoding.array Encoding.natural).encode (levelChoiceWeights vista r old.val weights))) := by
  let localStore : Store 30 := store ∘ levelSelectRoles
  have localWork (i : Fin 32) (small : i.val<17) (different : i≠1) : localStore i=[] := by
    apply work (levelSelectRoles i) small
    intro same;apply different
    exact Fin.ext (congrArg (fun j:Fin 40=>j.val) same)
  let index : Fin vista.nodes.toList.length := ⟨old.val,by simpa only [Array.length_toList] using old.isLt⟩
  have nodeEq : vista.nodes.toList[index]=(vista.node old.val) := by
    simp [index,Executable.Vista.node]
  obtain ⟨readTime,readBound,read⟩ := selectedLevel_executes localStore accepted tail status localWork e19
    vista.nodes.toList index (Encoding.natural.encode vista.bottom) table
    (by change (store 18).length=old.val;rw [counter,List.length_replicate]) r query
  rw [nodeEq] at read
  let flagged := Function.update store 31 [decide ((vista.node old.val).level=r)]
  have a : Executes (relocate selectedLevel levelSelectRoles) store readTime flagged := by
    apply relocate_executes_frame selectedLevel levelSelectRoles _ _ _ _ readTime rfl _ _ read
    · intro i;fin_cases i <;> simp [flagged,localStore,levelSelectRoles,e31]
    · intro i outside
      have n31 : i≠31 := by intro same;subst i;exact outside 31 rfl
      simp [flagged,n31]
  have restored : Function.update flagged 31 []=store := by
    simp only [flagged,Function.update_idem]
    rw [←e31,Function.update_eq_self]
  by_cases selected : (vista.node old.val).level=r
  · obtain ⟨time,bounded,body⟩ := updateCurrent_executes store accepted tail status work
      e19 e20 e21 e23 e24 e25 e26 e31 e33 e37 e38 vista weights length nodeInput weightInput
      r old.val (by rw [length];exact old.isLt) level counter
    have ready : Executes updateCurrent (Function.update flagged 31 []) time
        (Function.update store 35 ((Encoding.array Encoding.natural).encode (levelChoiceWeights vista r old.val weights))) := by
      rw [restored]
      simpa only [levelChoiceWeights,selected,if_true] using body
    have b := branch_executes_true (31:Fin 40) updateCurrent (skip 38) flagged _ [] time
      (by simp [flagged,selected]) ready
    refine ⟨_,?_,a.sequence b⟩
    change readTime ≤ 8000*((store 17).length+r.size+1)^4 at readBound
    omega
  · have body : Executes (skip 38) (Function.update flagged 31 []) 0 store := by
      rw [restored];exact skip_executes store
    have b := branch_executes_false (31:Fin 40) updateCurrent (skip 38) flagged store [] 0
      (by simp [flagged,selected]) body
    have final : Function.update store 35 ((Encoding.array Encoding.natural).encode (levelChoiceWeights vista r old.val weights))=store := by
      rw [levelChoiceWeights,if_neg selected,←weightInput,Function.update_eq_self]
    rw [final]
    refine ⟨_,?_,a.sequence b⟩
    change readTime ≤ 8000*((store 17).length+r.size+1)^4 at readBound
    omega

theorem levelItem_executes (store : Store 38) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ i : Fin 40,i.val<17 → i≠1 → store i=[])
    (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e23 : store 23=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (e26 : store 26=[]) (e31 : store 31=[]) (e33 : store 33=[])
    (e37 : store 37=[]) (e38 : store 38=[])
    (vista : Executable.Vista) (weights : Array Nat) (length : weights.size=vista.nodes.size)
    (nodeInput : store 34=Encoding.vista.encode vista)
    (table : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (weightInput : store 35=(Encoding.array Encoding.natural).encode weights)
    (r : Nat) (old : Fin vista.nodes.size)
    (level : store 22=(r+1).bits) (query : store 30=r.bits)
    (counter : store 18=List.replicate old.val true) :
    ∃ time ≤ 30000*((store 17).length+(store 34).length+(store 35).length+
        r.size+(r+1).size+old.val+2)^5,
      Executes levelItem store time
        (Function.update (Function.update store 35 ((Encoding.array Encoding.natural).encode
          (levelChoiceWeights vista r old.val weights))) 18 (List.replicate (old.val+1) true)) := by
  obtain ⟨time,bounded,a⟩ := levelChoice_executes store accepted tail status work e19 e20 e21 e23 e24 e25
    e26 e31 e33 e37 e38 vista weights length nodeInput table weightInput r old level query counter
  have b := pushBit_executes (18:Fin 40) true
    (Function.update store 35 ((Encoding.array Encoding.natural).encode (levelChoiceWeights vista r old.val weights)))
  simp only [Function.update_of_ne (by decide : (18:Fin 40)≠35),counter,←List.replicate_succ] at b
  refine ⟨_,?_,a.sequence b⟩
  let size := (store 17).length+(store 34).length+(store 35).length+r.size+(r+1).size+old.val+2
  have a4 : ((store 17).length+r.size+1)^4 ≤ size^4 := Nat.pow_le_pow_left (by dsimp only [size];omega) 4
  have b5 : ((store 34).length+(store 35).length+(r+1).size+old.val+2)^5 ≤ size^5 :=
    Nat.pow_le_pow_left (by dsimp only [size];omega) 5
  have one : 1 ≤ size := by dsimp only [size];omega
  have a5 : size^4 ≤ size^5 := Nat.pow_le_pow_right one (by decide)
  have positive : 1 ≤ size^5 := Nat.one_le_pow _ _ one
  change _ ≤ 30000*size^5
  omega

end Counting.StackMachine.AuditPropagation
