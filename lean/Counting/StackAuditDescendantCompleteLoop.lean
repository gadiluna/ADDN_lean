import Counting.StackAuditDescendantOuterItem

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def completeFile (vista : Executable.Vista) (weights : Array Nat) (anchor last start count : Nat)
    (accepted : Bool) : Store 46 := fun r=>
  if r=29 then (start+1).bits else if r=32 then (Encoding.array Encoding.natural).encode weights
  else if r=34 then last.bits else if r=38 then List.replicate (last-anchor) true
  else if r=40 then anchor.bits else if r=43 then List.replicate start true
  else if r=44 then List.replicate count true else if r=45 then [accepted]
  else if r=46 then (Encoding.array Encoding.node).encode vista.nodes else []

abbrev completeLoop : Routine 46 := forEach 44 outerItem

/-- Every actual stored node is considered as an anchor candidate. The inner
inequality routines and all loop control transitions are included in the bound. -/
theorem completeLoop_executes (vista : Executable.Vista) (weights : Array Nat)
    (anchor last start count : Nat) (inside : start+count≤vista.nodes.size) (accepted : Bool) :
    ∃ time ≤ count*(82000000000000*
        (((Encoding.array Encoding.node).encode vista.nodes).length+
          ((Encoding.array Encoding.natural).encode weights).length+(last-anchor)+anchor.size+last.size+1)^6+2)+1,
      Executes completeLoop (completeFile vista weights anchor last start count accepted) time
        (completeFile vista weights anchor last (start+count) 0
          (accepted && Executable.auditDescendantRange vista weights anchor last start count)) := by
  induction count generalizing start accepted with
  | zero=>
    let store:=completeFile vista weights anchor last start 0 accepted
    have empty : store 44=[] := by simp [store,completeFile]
    obtain ⟨run,halt⟩:=repeat_empty (44:Fin 48) outerItem store empty
    refine ⟨1,by simp,⟨1,store⟩,run,halt,?_⟩
    simp [store]
  | succ count ih=>
    let store:=completeFile vista weights anchor last start (count+1) accepted
    let popped:=completeFile vista weights anchor last start count accepted
    have consumed : Function.update store 44 (List.replicate count true)=popped := by
      funext r
      fin_cases r <;> simp [store,popped,completeFile]
    let index : Fin vista.nodes.size:=⟨start,by omega⟩
    have work (r:Fin 48) (small:r.val<40) (n29:r≠29) (n32:r≠32) (n34:r≠34) (n38:r≠38) : popped r=[] := by
      have n40:r≠40:=by intro eq;subst r;norm_num at small
      have n43:r≠43:=by intro eq;subst r;norm_num at small
      have n44:r≠44:=by intro eq;subst r;norm_num at small
      have n45:r≠45:=by intro eq;subst r;norm_num at small
      have n46:r≠46:=by intro eq;subst r;norm_num at small
      simp [popped,completeFile,n29,n32,n34,n38,n40,n43,n44,n45,n46]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=outerItem_executes popped vista weights
      anchor last index (List.replicate (last-anchor) true) (by simp) accepted []
      (by simp [popped,completeFile]) (by simp [popped,completeFile])
      (by simp [popped,completeFile,index]) (by simp [popped,completeFile])
      (by simp [popped,completeFile]) (by simp [popped,completeFile,index])
      (by simp [popped,completeFile]) (by simp [popped,completeFile]) work
    let hit:=Executable.auditAncestor vista weights anchor last start
    have middle : outerItemResult popped start accepted hit []=
        completeFile vista weights anchor last (start+1) count (accepted && hit) := by
      funext r
      fin_cases r <;> simp [outerItemResult,popped,completeFile,List.replicate_succ]
    change bodyFinish.store=outerItemResult popped start accepted hit [] at bodyStore
    rw [middle] at bodyStore
    have first:=repeat_iteration (44:Fin 48) outerItem store true (List.replicate count true)
      (by simp [store,completeFile,List.replicate_succ]) bodyTime bodyFinish
      (by rw [consumed];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih (start+1) (by omega) (accepted && hit)
    have final : completeFile vista weights anchor last (start+1+count) 0
        ((accepted && hit) && Executable.auditDescendantRange vista weights anchor last (start+1) count)=
        completeFile vista weights anchor last (start+(count+1)) 0
          (accepted && Executable.auditDescendantRange vista weights anchor last start (count+1)) := by
      simp only [Executable.auditDescendantRange_succ,Bool.and_assoc,hit,
        Nat.add_left_comm,Nat.add_comm]
    have table : popped 46=(Encoding.array Encoding.node).encode vista.nodes := by simp [popped,completeFile]
    have values : popped 32=(Encoding.array Encoding.natural).encode weights := by simp [popped,completeFile]
    rw [table,values,List.length_replicate] at bodyBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · rw [Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,first,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditDescendant
