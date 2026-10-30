import Counting.ExternalCoefficientGeometric
import Counting.StackLoop

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem geometricStepCost_mono {a b c a' b' c' : Nat} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    geometricStepCost a b c ≤ geometricStepCost a' b' c' := by
  unfold geometricStepCost NaturalPower.accumulatePowerCost NaturalPower.iterationCost
  gcongr

def geometricLoop (extra : Nat) (w : Workspace extra) : Routine (extra+62) := forEach (w 42) (geometricStep extra w)

theorem geometricLoop_executes (extra : Nat) (w : Workspace extra) (count boundIndex base sumLimit : Nat)
    (store : Fin (extra+64) → List Bool) (start initial : Nat)
    (baseInput : store (w 52)=base.bits) (accumulator : store (w 55)=initial.bits)
    (index : (store (w 37)).length=start) (counter : store (w 42)=List.replicate count true)
    (indexBound : start+count ≤ boundIndex) (sumSize : (initial+geometric base start count).bits.length ≤ sumLimit)
    (empty : ∀ i∈geometricScratch,store (w i)=[]) :
    ∃ time ≤ count*(geometricStepCost base.bits.length sumLimit boundIndex+2)+1,
      Executes (geometricLoop extra w) store time
        (Function.update (Function.update (Function.update store (w 42) []) (w 37)
          (List.replicate count true++store (w 37))) (w 55) (initial+geometric base start count).bits) := by
  induction count generalizing store start initial with
  | zero=>
    obtain ⟨ran,halted⟩:=repeat_empty (w 42) (geometricStep extra w) store counter
    have counterEmpty : store (w 42)=[] := counter
    refine ⟨1,by simp,⟨1,store⟩,ran,halted,?_⟩
    simp only [List.replicate_zero,List.nil_append,geometric,Nat.add_zero]
    rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,←accumulator,Function.update_eq_self]
  | succ count ih=>
    let consumed:=Function.update store (w 42) (List.replicate count true)
    have consumedEmpty (i : Fin 64) (member : i∈geometricScratch) : consumed (w i)=[] := by
      have different : i≠42 := by intro same;subst i;simp [geometricScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=geometricStep_executes extra w consumed consumedEmpty
    let next:=Function.update (Function.update consumed (w 55) (initial+base^start).bits) (w 37) (true::store (w 37))
    have bodyResult : bodyFinish.store=next := by
      simpa [next,consumed,w.injective.eq_iff,baseInput,accumulator,Encoding.value_bits,index] using bodyStore
    have nextEmpty (i : Fin 64) (member : i∈geometricScratch) : next (w i)=[] := by
      have n55 : i≠55 := by intro same;subst i;simp [geometricScratch] at member
      have n37 : i≠37 := by intro same;subst i;simp [geometricScratch] at member
      simpa [next,w.injective.eq_iff,n55,n37] using consumedEmpty i member
    have sameSum : initial+base^start+geometric base (start+1) count=initial+geometric base start (count+1) := by
      simp [geometric,Nat.add_assoc]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next (start+1) (initial+base^start)
      (by simp [next,consumed,w.injective.eq_iff,baseInput]) (by simp [next,w.injective.eq_iff])
      (by simp [next,index]) (by simp [next,consumed,w.injective.eq_iff]) (by omega) (by rwa [sameSum]) nextEmpty
    have firstRun:=repeat_iteration (w 42) (geometricStep extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (geometricLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have initialBound : initial.bits.length ≤ sumLimit := by
      apply le_trans _ sumSize
      simp only [Encoding.bits_length]
      exact Nat.size_le_size (Nat.le_add_right _ _)
    have bodyLimit : bodyTime ≤ geometricStepCost base.bits.length sumLimit boundIndex := by
      apply bodyBound.trans
      apply geometricStepCost_mono
      · simp [consumed,w.injective.eq_iff,baseInput]
      · simpa [consumed,w.injective.eq_iff,accumulator] using initialBound
      · simp only [consumed,Function.update_of_ne (show w 37≠w 42 by simp [w.injective.eq_iff]),index]
        omega
    refine ⟨bodyTime+2+tailTime,by nlinarith only [bodyLimit,tailBound],tailFinish,?_,tailHalt,?_⟩
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult];exact tailRun
    · rw [tailStore,sameSum]
      funext r
      by_cases e55 : r=w 55
      · subst r;simp
      · by_cases e37 : r=w 37
        · subst r
          simp only [Function.update_of_ne (show w 37≠w 55 by simp [w.injective.eq_iff]),Function.update_self,next]
          rw [List.replicate_succ']
          simp [List.append_assoc]
        · by_cases e42 : r=w 42
          · subst r;simp [w.injective.eq_iff]
          · simp [next,consumed,e55,e37,e42]

end Counting.External.CoefficientMachine
