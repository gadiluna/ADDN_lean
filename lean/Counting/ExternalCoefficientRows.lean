import Counting.ExternalCoefficientRow

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem rowCost_mono {s u b h l s' u' b' h' l' : Nat}
    (hs : s ≤ s') (hu : u ≤ u') (hb : b ≤ b') (hh : h ≤ h') (hl : l ≤ l') :
    rowCost s u b h l  ≤  rowCost s' u' b' h' l' := by
  unfold rowCost tripleCost
  have atom := atomCost_mono hs hu hb hl hu
  nlinarith only [atom,hh,hl]

def writeCoefficientRows (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  forEach (w 43) (writeCoefficientRow extra w)

def coefficientRowsResult (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (base high : Nat) (rows : List (List Nat)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 43) []) (w 36)
    ((Encoding.sequence Encoding.natural (rows.map (fun row=>high+powers base row))).reverse++store (w 36))

theorem writeCoefficientRows_executes (extra : Nat) (w : Workspace extra) (rows : List (List Nat))
    (base high universeLength sourceLimit sumLimit : Nat) (store : Fin (extra+64) → List Bool)
    (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rows++suffix)
    (counter : store (w 43)=List.replicate rows.length true)
    (status : store (w 1)=accepted::tail) (universeSize : (store (w 17)).length=universeLength)
    (baseInput : store (w 52)=base.bits) (highInput : store (w 54)=high.bits)
    (sourceBound : (store (w 0)).length ≤ sourceLimit)
    (three : ∀ row∈rows,row.length=3)
    (fits : ∀ row∈rows,∀ index∈row,index ≤ universeLength)
    (sumSize : ∀ row∈rows,(high+powers base row).bits.length ≤ sumLimit)
    (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time  ≤  rows.length*(rowCost sourceLimit universeLength base.bits.length high.bits.length sumLimit+2)+1,
      Executes (writeCoefficientRows extra w) store time (coefficientRowsResult w store base high rows suffix) := by
  induction rows generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (w 43) (writeCoefficientRow extra w) store counter
    have unchanged : coefficientRowsResult w store base high [] suffix=store := by
      simp only [coefficientRowsResult,List.map_nil,Encoding.sequence,List.reverse_nil,List.nil_append]
      have sourceEq : store (w 0)=suffix := source
      have counterEmpty : store (w 43)=[] := counter
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons row rest ih=>
    let consumed:=Function.update store (w 43) (List.replicate rest.length true)
    let remaining:=Encoding.sequence (Encoding.list Encoding.natural) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.list Encoding.natural).encode row++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 64) (member : i∈rowScratch) : consumed (w i)=[] := by
      have different : i≠43 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=writeCoefficientRow_executes extra w consumed
      base high row sumLimit accepted remaining tail consumedSource (three row (by simp))
      (by simp [consumed,w.injective.eq_iff,status])
      (by simp [consumed,w.injective.eq_iff,baseInput])
      (by simp [consumed,w.injective.eq_iff,highInput]) (sumSize row (by simp))
      (fun index member=>by simpa [consumed,w.injective.eq_iff,universeSize] using fits row (by simp) index member) consumedEmpty
    let next:=Function.update (Function.update consumed (w 0) remaining) (w 36)
      ((Encoding.natural.encode (high+powers base row)).reverse++consumed (w 36))
    have bodyResult : bodyFinish.store=next := bodyStore
    have nextSource : next (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rest++suffix := by
      simp [next,w.injective.eq_iff,remaining]
    have nextCounter : next (w 43)=List.replicate rest.length true := by simp [next,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,consumed,w.injective.eq_iff,status]
    have nextUniverse : (next (w 17)).length=universeLength := by simpa [next,consumed,w.injective.eq_iff] using universeSize
    have nextBase : next (w 52)=base.bits := by simp [next,consumed,w.injective.eq_iff,baseInput]
    have nextHigh : next (w 54)=high.bits := by simp [next,consumed,w.injective.eq_iff,highInput]
    have nextBound : (next (w 0)).length ≤ sourceLimit := by
      rw [nextSource];rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢;omega
    have nextEmpty (i : Fin 64) (member : i∈rowScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
      have b : i≠36 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
      simpa [next,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next nextSource nextCounter nextStatus
      nextUniverse nextBase nextHigh nextBound (fun row member=>three row (by simp [member]))
      (fun row member=>fits row (by simp [member])) (fun row member=>sumSize row (by simp [member])) nextEmpty
    have firstRun:=repeat_iteration (w 43) (writeCoefficientRow extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (writeCoefficientRows extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ rowCost sourceLimit universeLength base.bits.length high.bits.length sumLimit := by
      apply bodyBound.trans
      apply rowCost_mono
      · simpa [consumed,w.injective.eq_iff] using sourceBound
      · simp [consumed,w.injective.eq_iff,universeSize]
      all_goals rfl
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult];exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [coefficientRowsResult,w.injective.eq_iff]
      · by_cases e43 : r=w 43
        · subst r;simp [coefficientRowsResult,w.injective.eq_iff]
        · by_cases e36 : r=w 36
          · subst r;simp [coefficientRowsResult,next,consumed,w.injective.eq_iff,Encoding.sequence,List.reverse_append,List.append_assoc]
          · simp [coefficientRowsResult,next,consumed,e0,e43,e36]

end Counting.External.CoefficientMachine
