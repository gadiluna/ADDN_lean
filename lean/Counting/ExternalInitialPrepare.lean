import Counting.ExternalInitialFlags

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def initialPrepare (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  sequence (initialIndex extra w) (sequence (initialEnd extra w)
    (sequence (initialAfter extra w) (sequence (initialHead extra w)
      (sequence (initialLookup extra w) (initialOutside extra w)))))

def initialPrepared (w : InitialWorkspace extra) (store : Fin (extra+24) → List Bool)
    (place offset capacity : Nat) :=
  let index := place-offset
  let found := (store (w 2))[index]?
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update store (w 6) (List.replicate index true))
      (w 12) (List.replicate ((store (w 2)).length+capacity) true))
      (w 7) [decide (offset≤place)]) (w 8) [decide (place=offset)])
      (w 9) found.toList) (w 10) [found.isSome])
      (w 11) [decide ((store (w 2)).length+capacity≤ index)]

theorem initialPrepare_executes (extra : Nat) (w : InitialWorkspace extra) (place offset capacity : Nat)
    (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (capacityValue : store (w 3)=List.replicate capacity true)
    (empty : ∀ i ∈ ([6,7,8,9,10,11,12,13,14,15,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ 30*place+19*offset+17*(store (w 2)).length+11*capacity+59,
      Executes (initialPrepare extra w) store transitions (initialPrepared w store place offset capacity) := by
  let index := place-offset
  let stop := (store (w 2)).length+capacity
  let s₁ := Function.update store (w 6) (List.replicate index true)
  let s₂ := Function.update s₁ (w 12) (List.replicate stop true)
  let s₃ := Function.update s₂ (w 7) [decide (offset≤place)]
  let s₄ := Function.update s₃ (w 8) [decide (place=offset)]
  let found := (store (w 2))[index]?
  let s₅ := Function.update (Function.update s₄ (w 9) found.toList) (w 10) [found.isSome]
  have first := initialIndex_executes extra w place offset store placeValue offsetValue
    (empty 6 (by simp)) (empty 13 (by simp)) (empty 20 (by simp))
  have second : Executes (initialEnd extra w) s₁ (5*(store (w 2)).length+5*capacity+5) s₂ := by
    have run := initialEnd_executes extra w capacity s₁
      (by simp [s₁,w.injective.eq_iff,capacityValue])
      (by simp [s₁,w.injective.eq_iff,empty 12 (by simp)])
      (by simp [s₁,w.injective.eq_iff,empty 20 (by simp)])
    simpa [s₂,s₁,w.injective.eq_iff,stop] using run
  have third : Executes (initialAfter extra w) s₂ (6*(offset+place)+9) s₃ := by
    have run := initialAfter_executes extra w place offset s₂
      (by simp [s₂,s₁,w.injective.eq_iff,placeValue])
      (by simp [s₂,s₁,w.injective.eq_iff,offsetValue])
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl
        all_goals
          simp [s₂,s₁,w.injective.eq_iff]
          apply empty
          simp)
    simpa [s₃,s₂,s₁,w.injective.eq_iff,empty 7 (by simp)] using run
  obtain ⟨headTime,headBound,headRun⟩ := initialHead_executes extra w place offset s₃
    (by simp [s₃,s₂,s₁,w.injective.eq_iff,placeValue])
    (by simp [s₃,s₂,s₁,w.injective.eq_iff,offsetValue])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl
      all_goals
          simp [s₃,s₂,s₁,w.injective.eq_iff]
          apply empty
          simp)
  have fourth : Executes (initialHead extra w) s₃ headTime s₄ := by
    simpa [s₄,s₃,s₂,s₁,w.injective.eq_iff,empty 8 (by simp)] using headRun
  obtain ⟨lookupTime,lookupBound,lookupRun⟩ := initialLookup_executes extra w index s₄
    (by simp [s₄,s₃,s₂,s₁,w.injective.eq_iff])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl
      all_goals
          simp [s₄,s₃,s₂,s₁,w.injective.eq_iff]
          apply empty
          simp)
  have fifth : Executes (initialLookup extra w) s₄ lookupTime s₅ := by
    simpa [s₅,s₄,s₃,s₂,s₁,w.injective.eq_iff,found,empty 9 (by simp),empty 10 (by simp)] using lookupRun
  have sixth : Executes (initialOutside extra w) s₅ (6*(stop+index)+9)
      (initialPrepared w store place offset capacity) := by
    have run := initialOutside_executes extra w index stop s₅
      (by simp [s₅,s₄,s₃,s₂,s₁,w.injective.eq_iff])
      (by simp [s₅,s₄,s₃,s₂,w.injective.eq_iff])
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl
        all_goals
          simp [s₅,s₄,s₃,s₂,s₁,w.injective.eq_iff]
          apply empty
          simp)
    simpa [initialPrepared,s₅,s₄,s₃,s₂,s₁,found,index,stop,w.injective.eq_iff,empty 11 (by simp)] using run
  have combined := first.sequence (second.sequence (third.sequence (fourth.sequence (fifth.sequence sixth))))
  refine ⟨5*place+7*offset+7+1+(5*(store (w 2)).length+5*capacity+5+1+
      (6*(offset+place)+9+1+(headTime+1+(lookupTime+1+(6*(stop+index)+9))))),?_,combined⟩
  simp only [s₄,s₃,s₂,s₁,Function.update_of_ne (show w 2 ≠ w 8 by simp [w.injective.eq_iff]),
    Function.update_of_ne (show w 2 ≠ w 7 by simp [w.injective.eq_iff]),
    Function.update_of_ne (show w 2 ≠ w 12 by simp [w.injective.eq_iff]),
    Function.update_of_ne (show w 2 ≠ w 6 by simp [w.injective.eq_iff])] at lookupBound
  have indexBound : index≤place := Nat.sub_le _ _
  dsimp only [stop]
  omega

end Counting.External.CookLevin.StackGenerator
