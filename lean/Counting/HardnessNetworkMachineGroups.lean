import Counting.HardnessNetworkMachineGroup

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev GroupsWorkspace (extra : Nat) := Fin 13 ↪ Fin (extra+13)
def groupsPositions : Fin 12 ↪ Fin 13 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 13=>i.val) h)⟩
def GroupsWorkspace.group (w : GroupsWorkspace extra) : GroupWorkspace (extra+1) := groupsPositions.trans w

theorem ordinaryGroupRows_succ (width start size count : Nat) :
    ordinaryGroupRows width start size (count+1)=
      groupRows width start size++ordinaryGroupRows width (start+size) size count := by
  simp only [ordinaryGroupRows,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,Nat.zero_mul,Nat.add_zero]
  congr 1
  apply congrArg (fun f : Nat → List (List Nat)=>(List.range count).flatMap f)
  funext index
  congr 1
  rw [Nat.succ_eq_add_one]
  ring

def emitGroups (extra : Nat) (w : GroupsWorkspace extra) : Routine (extra+11) :=
  forEach (w 12) (emitGroup (extra+1) w.group)

def groupsResult (w : GroupsWorkspace extra) (store : Fin (extra+13) → List Bool) (start size count : Nat) :=
  Function.update (Function.update (Function.update store (w 12) [])
    (w 1) (List.replicate (count*size) true++store (w 1))) (w 2)
    ((Encoding.sequence (Encoding.list Encoding.natural)
      (ordinaryGroupRows (store (w 0)).length start size count)).reverse++store (w 2))

theorem emitGroups_executes (extra : Nat) (w : GroupsWorkspace extra) (start size count : Nat)
    (store : Fin (extra+13) → List Bool) (positive : 0<size)
    (index : (store (w 1)).length=start+1) (sizeValue : store (w 10)=List.replicate size true)
    (counter : store (w 12)=List.replicate count true)
    (inside : start+count*size ≤ (store (w 0)).length)
    (empty : ∀ i∈groupScratch,store (w.group i)=[]) :
    ∃ time ≤ count*(groupCost (store (w 0)).length size+2)+1,
      Executes (emitGroups extra w) store time (groupsResult w store start size count) := by
  induction count generalizing start store with
  | zero=>
    obtain ⟨ran,halted⟩:=repeat_empty (w 12) (emitGroup (extra+1) w.group) store counter
    have same : groupsResult w store start size 0=store := by
      simp only [groupsResult,ordinaryGroupRows,List.range_zero,List.flatMap_nil,Encoding.sequence,List.reverse_nil,List.nil_append,
        Nat.zero_mul,List.replicate_zero]
      have nil : store (w 12)=[]:=counter
      rw [←nil,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | succ count ih=>
    let consumed:=Function.update store (w 12) (List.replicate count true)
    have consumedEmpty (i : Fin 12) (member : i∈groupScratch) : consumed (w.group i)=[] := by
      have different : w.group i≠w 12 := by
        intro same
        have value:=congrArg Fin.val (w.injective same)
        change i.val=12 at value
        omega
      simpa [consumed,different] using empty i member
    have bodyInside : start+size ≤ (consumed (w.group 0)).length := by
      simp only [GroupsWorkspace.group,groupsPositions,Function.Embedding.trans_apply,Function.Embedding.coeFn_mk]
      change start+size ≤ (consumed (w 0)).length
      simp only [consumed,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 13)≠12))]
      nlinarith only [inside,Nat.zero_le (count*size)]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=emitGroup_executes (extra+1) w.group start size consumed positive
      (by simpa [GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff] using index)
      (by simpa [GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff] using sizeValue)
      bodyInside consumedEmpty
    let next:=groupResult w.group consumed start size
    have nextIndex : (next (w 1)).length=(start+size)+1 := by
      simp [next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff,index]
      omega
    have nextSize : next (w 10)=List.replicate size true := by
      simp [next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff,sizeValue]
    have nextCounter : next (w 12)=List.replicate count true := by
      simp [next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff]
    have widthAt : next (w 0)=store (w 0) := by
      simp [next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff]
    have nextInside : (start+size)+count*size ≤ (next (w 0)).length := by
      rw [widthAt];nlinarith only [inside]
    have nextEmpty (i : Fin 12) (member : i∈groupScratch) : next (w.group i)=[] := by
      have a : i≠1 := by intro eq;subst i;simp [groupScratch] at member
      have b : i≠2 := by intro eq;subst i;simp [groupScratch] at member
      simpa [next,groupResult,w.group.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih (start+size) next nextIndex nextSize nextCounter nextInside nextEmpty
    rw [widthAt] at tailBound
    have firstRun:=repeat_iteration (w 12) (emitGroup (extra+1) w.group) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitGroups extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ groupCost (store (w 0)).length size := by
      simpa [GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff] using bodyBound
    refine ⟨bodyTime+2+tailTime,by nlinarith only [bodyLimit,tailBound],tailFinish,?_,tailHalt,?_⟩
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore];exact tailRun
    · rw [tailStore]
      funext r
      by_cases e12 : r=w 12
      · subst r;simp [groupsResult,w.injective.eq_iff]
      · by_cases e1 : r=w 1
        · subst r
          simp [groupsResult,next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff,
            ←List.append_assoc,Nat.add_mul]
        · by_cases e2 : r=w 2
          · subst r
            simp [groupsResult,next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,w.injective.eq_iff,
              ordinaryGroupRows_succ,sequence_append,List.reverse_append,List.append_assoc]
          · simp [groupsResult,next,groupResult,GroupsWorkspace.group,groupsPositions,consumed,e12,e1,e2]

end Counting.HardnessNetworkMachine
