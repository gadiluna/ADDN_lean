import Counting.HardnessNetworkMachineLeaderBlock

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def emitLeaderBlocks (extra : Nat) (w : LeaderWorkspace extra) : Routine (extra+38) :=
  forEach (w 23) (emitLeaderBlock extra w)

def leaderBlocksResult (w : LeaderWorkspace extra) (store : Fin (extra+40) → List Bool)
    (values : List Nat) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 23) []) (w 35)
    ((Encoding.sequence Encoding.natural (values.flatMap (List.replicate (store (w 33)).length))).reverse++store (w 35))

theorem emitLeaderBlocks_executes (extra : Nat) (w : LeaderWorkspace extra) (values : List Nat)
    (limit : Nat) (store : Fin (extra+40) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence Encoding.natural values++suffix)
    (counter : store (w 23)=List.replicate values.length true)
    (status : store (w 1)=accepted::tail) (sourceBound : (store (w 0)).length ≤ limit)
    (empty : ∀ i∈leaderBlockScratch,store (w i)=[]) :
    ∃ time ≤ values.length*(leaderBlockCost limit (store (w 33)).length+2)+1,
      Executes (emitLeaderBlocks extra w) store time (leaderBlocksResult w store values suffix) := by
  induction values generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (w 23) (emitLeaderBlock extra w) store counter
    have same : leaderBlocksResult w store [] suffix=store := by
      simp only [leaderBlocksResult,List.flatMap_nil,Encoding.sequence,List.reverse_nil,List.nil_append]
      have s : store (w 0)=suffix:=source
      have c : store (w 23)=[]:=counter
      rw [←s,Function.update_eq_self,←c,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | cons value rest ih=>
    let consumed:=Function.update store (w 23) (List.replicate rest.length true)
    let remaining:=Encoding.sequence Encoding.natural rest++suffix
    have consumedSource : consumed (w 0)=Encoding.natural.encode value++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 40) (member : i∈leaderBlockScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro eq;subst i;simp [leaderBlockScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=
      emitLeaderBlock_executes extra w consumed value accepted remaining tail consumedSource
        (by simp [consumed,w.injective.eq_iff,status]) consumedEmpty
    let next:=Function.update (Function.update consumed (w 0) remaining) (w 35)
      ((Encoding.sequence Encoding.natural (List.replicate (store (w 33)).length value)).reverse++store (w 35))
    have bodyResult : bodyFinish.store=next := by simpa [consumed,w.injective.eq_iff,next] using bodyStore
    have nextSource : next (w 0)=Encoding.sequence Encoding.natural rest++suffix := by simp [next,w.injective.eq_iff,remaining]
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,consumed,w.injective.eq_iff,status]
    have nextBound : (next (w 0)).length ≤ limit := by
      rw [nextSource];rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢;omega
    have nextEmpty (i : Fin 40) (member : i∈leaderBlockScratch) : next (w i)=[] := by
      have a : i≠0 := by intro eq;subst i;simp [leaderBlockScratch] at member
      have b : i≠35 := by intro eq;subst i;simp [leaderBlockScratch] at member
      simpa [next,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next nextSource nextCounter nextStatus nextBound nextEmpty
    have firstRun:=repeat_iteration (w 23) (emitLeaderBlock extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (emitLeaderBlocks extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have countAt : (next (w 33)).length=(store (w 33)).length := by simp [next,consumed,w.injective.eq_iff]
    rw [countAt] at tailBound
    have bodyLimit : bodyTime ≤ leaderBlockCost limit (store (w 33)).length := by
      apply bodyBound.trans
      have count : consumed (w 33)=store (w 33) := by simp [consumed,w.injective.eq_iff]
      have src : (consumed (w 0)).length ≤ limit := by simpa [consumed,w.injective.eq_iff] using sourceBound
      rw [count]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right src 1))) _
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult];exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [leaderBlocksResult,w.injective.eq_iff]
      · by_cases e23 : r=w 23
        · subst r;simp [leaderBlocksResult,w.injective.eq_iff]
        · by_cases e35 : r=w 35
          · subst r;simp [leaderBlocksResult,next,consumed,w.injective.eq_iff,List.flatMap_cons,sequence_append,List.reverse_append,List.append_assoc]
          · simp [leaderBlocksResult,next,consumed,e0,e23,e35]

end Counting.HardnessNetworkMachine
