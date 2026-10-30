import Counting.StackEncodingCountBody
import Counting.StackEncodingLoop

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def countState (extra : Nat) (w : CountWorkspace extra) (base : Fin (extra+11) → List Bool)
    (header : List Bool) (current : Nat) (budget : List Bool) : Fin (extra+11) → List Bool :=
  fun r => if r=w 0 then Encoding.frame header else if r=w 1 then List.replicate current true
    else if r=w 10 then budget else base r

theorem frame_injective : Function.Injective Encoding.frame := by
  intro a b equal
  have decoded := congrArg (fun input => Encoding.unframe (input++[])) equal
  simpa only [Encoding.unframe_frame,Option.some.injEq,Prod.mk.injEq,and_true] using decoded

theorem countState_body (extra : Nat) (w : CountWorkspace extra) (base : Fin (extra+11) → List Bool)
    (header : List Bool) (current : Nat) (budget : List Bool) :
    countBodyResult extra w (countState extra w base header current budget) =
      countState extra w base header (countNext header current) budget := by
  have compare : Encoding.natural.encode current=Encoding.frame header ↔ current.bits=header :=
    frame_injective.eq_iff
  simp only [countBodyResult,countState,w.injective.eq_iff]
  simp only [show (0:Fin 11)≠1 by decide,show (1:Fin 11)≠0 by decide,if_false,ite_true,List.length_replicate]
  by_cases same : current.bits=header
  · rw [if_pos (compare.mpr same)]
    simp only [countNext,same,ite_true]
  · rw [if_neg (fun equal => same (compare.mp equal))]
    simp only [countNext,same,if_false]
    funext r
    by_cases a : r=w 0
    · subst r; simp [countState,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r; simp [countState,w.injective.eq_iff,List.replicate_succ]
      · simp [countState,a,b]

theorem countState_budget (extra : Nat) (w : CountWorkspace extra) (base : Fin (extra+11) → List Bool)
    (header : List Bool) (current : Nat) (old budget : List Bool) :
    Function.update (countState extra w base header current old) (w 10) budget =
      countState extra w base header current budget := by
  funext r
  by_cases a : r=w 10
  · subst r; simp [countState,w.injective.eq_iff]
  · simp [countState,a]

def countLoop (extra : Nat) (w : CountWorkspace extra) : Routine (extra+9) :=
  Routine.forEach (w 10) (countBody extra w)

/-- Actual execution of the input-budgeted loop. The header may be malformed
or encode an arbitrarily large number: the loop still has at most one body
execution per supplied budget bit. -/
theorem countLoop_executes (extra : Nat) (w : CountWorkspace extra)
    (base : Fin (extra+11) → List Bool) (header : List Bool)
    (empty : ∀ i : Fin 11, i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → base (w i)=[])
    (budget : List Bool) (current limit : Nat) (bounded : current+budget.length≤limit) :
    ∃ time ≤ budget.length*(60*(limit+(Encoding.frame header).length+1)^2+2)+1,
      Routine.Executes (countLoop extra w) (countState extra w base header current budget) time
        (countState extra w base header (countRun header current budget.length) []) := by
  induction budget generalizing current with
  | nil =>
    have source : countState extra w base header current [] (w 10)=[] := by simp [countState,w.injective.eq_iff]
    obtain ⟨ran,halted⟩ := Routine.repeat_empty (w 10) (countBody extra w) _ source
    exact ⟨1,by simp,⟨⟨1,_⟩,ran,halted,rfl⟩⟩
  | cons bit budget ih =>
    let start := countState extra w base header current (bit::budget)
    let consumed := countState extra w base header current budget
    have work : ∀ i : Fin 11, i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → consumed (w i)=[] := by
      intro i member
      have not0 : i≠0 := by intro eq; subst i; exact (by decide : (0:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
      have not1 : i≠1 := by intro eq; subst i; exact (by decide : (1:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
      have not10 : i≠10 := by intro eq; subst i; exact (by decide : (10:Fin 11)∉({2,3,4,5,7,8,9}:Finset (Fin 11))) member
      simpa only [consumed,countState,w.injective.eq_iff,if_neg not0,if_neg not1,if_neg not10] using empty i member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=countBody_executes extra w consumed work
    have source : start (w 10)=bit::budget := by simp [start,countState,w.injective.eq_iff]
    have changed : Function.update start (w 10) budget=consumed := countState_budget extra w base header current _ _
    have firstRun := Routine.repeat_iteration (w 10) (countBody extra w) start bit budget source bodyTime finishBody
      (by simpa only [changed] using bodyRun) bodyHalt
    change Machine.run (step (countLoop extra w).program) (bodyTime+2)
      ⟨0,countState extra w base header current (bit::budget)⟩ = some ⟨0,finishBody.store⟩ at firstRun
    have result : finishBody.store=countState extra w base header (countNext header current) budget :=
      bodyStore.trans (countState_body extra w base header current budget)
    have nextBound : countNext header current+budget.length≤limit := by
      have next := countNext_le header current
      simp only [List.length_cons] at bounded
      omega
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih (countNext header current) nextBound
    have currentBound : current≤limit := by omega
    have bodyTimeBound : bodyTime≤60*(limit+(Encoding.frame header).length+1)^2 := by
      have source0 : consumed (w 0)=Encoding.frame header := by simp [consumed,countState]
      have source1 : consumed (w 1)=List.replicate current true := by simp [consumed,countState,w.injective.eq_iff]
      rw [source0,source1,List.length_replicate] at bodyBound
      exact bodyBound.trans (by gcongr)
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,result]
      exact tailRun
    · exact tailStore

/-- Successful bounded conversion means the header has a canonical payload
whose value fits in the explicit budget. -/
theorem countLoop_final_accepted (header : List Bool) (budget : Nat) :
    Encoding.natural.encode (countRun header 0 budget)=Encoding.frame header ↔
      ∃ value≤budget, header=value.bits := by
  change Encoding.frame (countRun header 0 budget).bits=Encoding.frame header ↔ _
  rw [frame_injective.eq_iff,countRun_accept_iff]

end Counting.StackMachine.EncodingPrograms
