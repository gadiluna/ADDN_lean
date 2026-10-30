import Counting.StackAuditPrefixCountItem
import Counting.StackLoop

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev countLoop (mode : HeaderMode) : Routine 34 := forEach 28 (countItem mode)

def countResult (store : Store 34) (start count matched : Nat) : Store 34 :=
  Function.update (Function.update (Function.update store 18 (List.replicate (start+count) true)) 28 [])
    29 (List.replicate matched true++store 29)

def countBudget (source : List Bool) (level parent count : Nat) : Nat :=
  count*(10020*(source.length+level.size+parent.size+1)^4+2)+1

/-- Count a selected header predicate on precisely the physical index
interval supplied by the finite countdown. Both label queries and the
complete node table are retained, and all temporary flags are cleared. -/
theorem countLoop_executes (mode : HeaderMode) (vista : Executable.Vista)
    (store : Store 34) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (level parent start count : Nat) (inside : start+count ≤ vista.nodes.size)
    (index : store 18=List.replicate start true) (countdown : store 28=List.replicate count true)
    (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ countBudget (store 17) level parent count,
      Executes (countLoop mode) store time
        (countResult store start count (countRange vista mode level parent start count)) := by
  induction count generalizing start store with
  | zero=>
    have empty : store 28=[] := by simpa using countdown
    obtain ⟨run,halt⟩:=repeat_empty (28:Fin 36) (countItem mode) store empty
    have final : countResult store start 0 (countRange vista mode level parent start 0)=store := by
      simp only [countRange_zero,countResult,Nat.add_zero,List.replicate_zero,List.nil_append]
      rw [←index,Function.update_eq_self,←empty,Function.update_eq_self,Function.update_eq_self]
    refine ⟨1,by simp [countBudget],⟨1,store⟩,run,halt,final.symm⟩
  | succ count ih=>
    let popped:=Function.update store 28 (List.replicate count true)
    let nodeIndex : Fin vista.nodes.toList.length:=⟨start,by simpa using (show start<vista.nodes.size by omega)⟩
    have nodeAt : vista.nodes.toList[nodeIndex]=vista.node start := by
      simp [nodeIndex,Executable.Vista.node,show start<vista.nodes.size by omega]
    have poppedWork (r : Fin 36) (small : r.val<17) (different : r≠1) : popped r=[] := by
      have not28 : r≠28 := by intro equal;subst r;norm_num at small
      simpa [popped,not28] using work r small different
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=countItem_executes mode popped accepted tail
      (by simp [popped,status]) poppedWork (by simp [popped,e19])
      (by simp [popped,e31]) (by simp [popped,e33]) (by simp [popped,e34]) (by simp [popped,e35])
      vista.nodes.toList nodeIndex suffix (by simp [popped,input])
      (by simp [popped,index,nodeIndex]) level parent (by simp [popped,levelAt]) (by simp [popped,parentAt])
    rw [nodeAt] at bodyStore
    let hit:=nodeMatches mode (vista.node start) level parent
    let next:=itemStore popped hit
    have nextWork (r : Fin 36) (small : r.val<17) (different : r≠1) : next r=[] := by
      have not18 : r≠18 := by intro equal;subst r;norm_num at small
      have not29 : r≠29 := by intro equal;subst r;norm_num at small
      simpa [next,itemStore,not18,not29] using poppedWork r small different
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih next
      (by simp [next,itemStore,popped,status]) nextWork
      (by simp [next,itemStore,popped,e19]) (by simp [next,itemStore,popped,e31])
      (by simp [next,itemStore,popped,e33]) (by simp [next,itemStore,popped,e34])
      (by simp [next,itemStore,popped,e35]) (by simp [next,itemStore,popped,input])
      (start+1) (by omega) (by simp [next,itemStore,popped,index,List.replicate_succ])
      (by simp [next,itemStore,popped]) (by simp [next,itemStore,popped,levelAt])
      (by simp [next,itemStore,popped,parentAt])
    have firstRun:=repeat_iteration (28:Fin 36) (countItem mode) store true (List.replicate count true)
      (by simp [countdown,List.replicate_succ]) bodyTime finishBody bodyRun bodyHalt
    have final : countResult next (start+1) count (countRange vista mode level parent (start+1) count)=
        countResult store start (count+1) (countRange vista mode level parent start (count+1)) := by
      rw [countRange_succ]
      funext r
      by_cases r18 : r=18
      · subst r;simp [countResult,Nat.add_left_comm,Nat.add_comm]
      · by_cases r28 : r=28
        · subst r;simp [countResult]
        · by_cases r29 : r=29
          · subst r
            change List.replicate (countRange vista mode level parent (start+1) count) true ++
              (List.replicate (if hit then 1 else 0) true++store 29)=
              List.replicate ((if hit then 1 else 0)+countRange vista mode level parent (start+1) count) true++store 29
            rw [←List.append_assoc,List.replicate_append_replicate,Nat.add_comm]
          · simp [countResult,next,itemStore,popped,r18,r28,r29]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
    · have sameSource : popped 17=store 17 := by simp [popped]
      rw [sameSource] at bodyBound
      have nextSource : next 17=store 17 := by simp [next,itemStore,popped]
      rw [nextSource] at tailBound
      dsimp only [countBudget] at tailBound ⊢
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditPrefix
