import Counting.StackAuditPrefixCountLoop

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev countAll (mode : HeaderMode) : Routine 34 :=
  sequence (ofProgram (ListPrograms.copyProgram 33 20 28 4))
    (sequence (countLoop mode) (clear 18))

/-- The full traversal is prepared by copying the stored unary node
budget, and its physical index is erased on return. The resulting unary
count is bounded by the actual table size, independently of label values. -/
theorem countAll_executes (mode : HeaderMode) (vista : Executable.Vista)
    (store : Store 34) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (level parent : Nat) (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 20000*((store 17).length+level.size+parent.size+1)^5,
      Executes (countAll mode) store time
        (Function.update store 29
          (List.replicate (countRange vista mode level parent 0 vista.nodes.size) true++store 29)) := by
  have a:=copy_executes 33 (20:Fin 36) 28 4 (by decide) (by decide) (by decide) store
    (work _ (by decide) (by decide))
  rw [nodeCount,e28,List.append_nil,List.length_replicate] at a
  let ready:=Function.update store 28 (List.replicate vista.nodes.size true)
  have readyWork (r : Fin 36) (small : r.val<17) (different : r≠1) : ready r=[] := by
    have not28 : r≠28 := by intro equal;subst r;norm_num at small
    simpa [ready,not28] using work r small different
  obtain ⟨loopTime,loopBound,b⟩:=countLoop_executes mode vista ready accepted tail
    (by simp [ready,status]) readyWork (by simp [ready,e19]) (by simp [ready,e31])
    (by simp [ready,e33]) (by simp [ready,e34]) (by simp [ready,e35]) suffix
    (by simp [ready,input]) level parent 0 vista.nodes.size (by omega)
    (by simp [ready,e18]) (by simp [ready]) (by simp [ready,levelAt]) (by simp [ready,parentAt])
  let amount:=countRange vista mode level parent 0 vista.nodes.size
  let scanned:=countResult ready 0 vista.nodes.size amount
  have c:=clear_executes (18:Fin 36) scanned
  have physicalIndex : scanned 18=List.replicate vista.nodes.size true := by simp [scanned,countResult]
  rw [physicalIndex,List.length_replicate] at c
  have final : Function.update scanned 18 []=
      Function.update store 29 (List.replicate amount true++store 29) := by
    funext r
    by_cases r18 : r=18
    · subst r;simp [e18]
    · by_cases r28 : r=28
      · subst r;simp [scanned,countResult,ready,e28]
      · by_cases r29 : r=29
        · subst r;simp [scanned,countResult,ready]
        · simp [scanned,countResult,ready,r18,r28,r29]
  rw [final] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  let S:=(store 17).length+level.size+parent.size+1
  have lengthBound:=DagValidation.node_sequence_count_le vista.nodes.toList
  have nodes : vista.nodes.size ≤ S := by
    simp only [Array.length_toList] at lengthBound
    dsimp only [S]
    rw [input,List.length_append]
    omega
  have loopLimit : loopTime ≤ S*(10020*S^4+2)+1 := by
    apply loopBound.trans
    change vista.nodes.size*(10020*((ready 17).length+level.size+parent.size+1)^4+2)+1 ≤ _
    have sourceAt : ready 17=store 17 := by simp [ready]
    rw [sourceAt]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ nodes) 1
  have expanded : S*(10020*S^4+2)+1=10020*S^5+2*S+1 := by ring
  rw [expanded] at loopLimit
  have linear : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change 5*vista.nodes.size+2+1+(loopTime+1+(vista.nodes.size+1)) ≤ 20000*S^5
  omega

end Counting.StackMachine.AuditPrefix
