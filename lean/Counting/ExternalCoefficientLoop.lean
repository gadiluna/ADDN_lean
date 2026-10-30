import Counting.ExternalCoefficientAtom
import Counting.StackLoop

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def powers (base : Nat) (indices : List Nat) := (indices.map (fun e=>base^e)).sum

@[simp] theorem powers_nil (base : Nat) : powers base []=0 := rfl
@[simp] theorem powers_cons (base head : Nat) (tail : List Nat) : powers base (head::tail)=base^head+powers base tail := rfl

theorem atomCost_mono {a b c d e a' b' c' d' e' : Nat}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d') (he : e ≤ e') :
    atomCost a b c d e ≤ atomCost a' b' c' d' e' := by
  unfold atomCost NaturalPower.accumulatePowerCost NaturalPower.iterationCost
  gcongr

def coefficientAtoms (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  forEach (w 23) (coefficientAtom extra w)

theorem coefficientAtoms_executes (extra : Nat) (w : Workspace extra) (indices : List Nat)
    (sourceBound universeBound base sumLimit : Nat) (store : Fin (extra+64) → List Bool)
    (initial : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence Encoding.natural indices++suffix)
    (sourceSize : (store (w 0)).length ≤ sourceBound)
    (universeSize : (store (w 17)).length=universeBound)
    (baseInput : store (w 52)=base.bits) (accumulator : store (w 55)=initial.bits)
    (sumSize : (initial+powers base indices).bits.length ≤ sumLimit)
    (fits : ∀ e∈indices,e ≤ universeBound) (counter : store (w 23)=List.replicate indices.length true)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈atomScratch,store (w i)=[]) :
    ∃ time ≤ indices.length*(atomCost sourceBound universeBound base.bits.length sumLimit universeBound+2)+1,
      Executes (coefficientAtoms extra w) store time
        (Function.update (Function.update (Function.update store (w 23) []) (w 0) suffix) (w 55)
          (initial+powers base indices).bits) := by
  induction indices generalizing store initial with
  | nil =>
    obtain ⟨ran,halted⟩:=repeat_empty (w 23) (coefficientAtom extra w) store counter
    have sourceSame : store (w 0)=suffix := by simpa [Encoding.sequence] using source
    have counterSame : store (w 23)=[] := counter
    refine ⟨1,by simp,⟨1,store⟩,ran,halted,?_⟩
    simp only [powers_nil,Nat.add_zero,←accumulator,←sourceSame,←counterSame,
      Function.update_eq_self]
  | cons head rest ih =>
    let restSource:=Encoding.sequence Encoding.natural rest++suffix
    let consumed:=Function.update store (w 23) (List.replicate rest.length true)
    have consumedEmpty (i : Fin 64) (member : i∈atomScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [atomScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=coefficientAtom_executes extra w consumed head accepted restSource tail
      (by simpa [consumed,w.injective.eq_iff,Encoding.sequence,List.append_assoc,restSource] using source)
      (by simp [consumed,w.injective.eq_iff,status])
      (by simpa [consumed,w.injective.eq_iff,universeSize] using fits head (by simp)) consumedEmpty
    let next:=Function.update (Function.update consumed (w 0) restSource) (w 55) (initial+base^head).bits
    have bodyResult : bodyFinish.store=next := by
      simpa [next,consumed,w.injective.eq_iff,accumulator,baseInput,Encoding.value_bits] using bodyStore
    have nextEmpty (i : Fin 64) (member : i∈atomScratch) : next (w i)=[] := by
      have n0 : i≠0 := by intro same;subst i;simp [atomScratch] at member
      have n55 : i≠55 := by intro same;subst i;simp [atomScratch] at member
      simpa [next,w.injective.eq_iff,n0,n55] using consumedEmpty i member
    have nextSource : next (w 0)=restSource := by simp [next,w.injective.eq_iff]
    have suffixBound : restSource.length ≤ sourceBound := by
      rw [source] at sourceSize
      simpa only [Encoding.sequence,List.length_append,restSource] using
        (show (Encoding.sequence Encoding.natural rest++suffix).length ≤ sourceBound by
          simp only [Encoding.sequence,List.length_append] at sourceSize ⊢;omega)
    have sameSum : initial+base^head+powers base rest=initial+powers base (head::rest) := by simp [Nat.add_assoc]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next (initial+base^head)
      nextSource (by rw [nextSource];exact suffixBound)
      (by simp [next,consumed,w.injective.eq_iff,universeSize])
      (by simp [next,consumed,w.injective.eq_iff,baseInput]) (by simp [next])
      (by rwa [sameSum]) (fun e member=>fits e (by simp [member]))
      (by simp [next,consumed,w.injective.eq_iff]) (by simp [next,consumed,w.injective.eq_iff,status]) nextEmpty
    have firstRun:=repeat_iteration (w 23) (coefficientAtom extra w) store true (List.replicate rest.length true)
      (by simpa [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (coefficientAtoms extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have initialBound : initial.bits.length ≤ sumLimit := by
      apply le_trans _ sumSize
      simp only [Encoding.bits_length]
      exact Nat.size_le_size (Nat.le_add_right _ _)
    have bodyLimit : bodyTime ≤ atomCost sourceBound universeBound base.bits.length sumLimit universeBound := by
      apply bodyBound.trans
      apply atomCost_mono
      · simpa [consumed,w.injective.eq_iff] using sourceSize
      · simp [consumed,w.injective.eq_iff,universeSize]
      · simp [consumed,w.injective.eq_iff,baseInput]
      · simpa [consumed,w.injective.eq_iff,accumulator] using initialBound
      · exact fits head (by simp)
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult];exact tailRun
    · rw [tailStore,sameSum]
      funext r
      by_cases e55 : r=w 55
      · subst r;simp
      · by_cases e0 : r=w 0
        · subst r;simp [w.injective.eq_iff]
        · by_cases e23 : r=w 23
          · subst r;simp [w.injective.eq_iff]
          · simp [next,consumed,e55,e0,e23]

end Counting.External.CoefficientMachine
