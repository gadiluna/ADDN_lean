import Counting.StackEncodingListSemantics

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def listState (extra : Nat) (w : ListWorkspace extra) (base : Fin (extra+8) → List Bool)
    (input reversed : List Bool) (accepted : Bool) (tail counter : List Bool) : Fin (extra+8) → List Bool :=
  fun r => if r=w 0 then input else if r=w 3 then accepted::tail
    else if r=w 6 then reversed else if r=w 7 then counter else base r

theorem listState_item (extra : Nat) (w : ListWorkspace extra) (base : Fin (extra+8) → List Bool)
    (input reversed : List Bool) (accepted : Bool) (tail counter : List Bool) :
    listItemResult extra w (listState extra w base input reversed accepted tail counter) accepted tail =
      listState extra w base (unframeSuffix input) ((Encoding.frame (unframePayload input)).reverse++reversed)
        (accepted && itemAccepted input) tail counter := by
  funext r
  by_cases a : r=w 0
  · subst r; simp [listItemResult,listState,w.injective.eq_iff]
  · by_cases b : r=w 3
    · subst r; simp [listItemResult,listState,w.injective.eq_iff]
    · by_cases c : r=w 6
      · subst r; simp [listItemResult,listState,w.injective.eq_iff]
      · simp [listItemResult,listState,a,b,c,w.injective.eq_iff]

theorem listState_counter (extra : Nat) (w : ListWorkspace extra) (base : Fin (extra+8) → List Bool)
    (input reversed : List Bool) (accepted : Bool) (tail old counter : List Bool) :
    Function.update (listState extra w base input reversed accepted tail old) (w 7) counter =
      listState extra w base input reversed accepted tail counter := by
  funext r
  by_cases a : r=w 7
  · subst r; simp [listState,w.injective.eq_iff]
  · simp [listState,a]

def listLoop (extra : Nat) (w : ListWorkspace extra) : Routine (extra+6) :=
  Routine.forEach (w 7) (listItem extra w)

/-- Every input is processed within a bound polynomial in the explicit
counter and input lengths. Failure is sticky, and all scratch is restored
on every iteration, including truncated and noncanonical fields. -/
theorem listLoop_executes (extra : Nat) (w : ListWorkspace extra)
    (base : Fin (extra+8) → List Bool)
    (empty : ∀ i : Fin 8, i∈({1,2,4,5}:Finset (Fin 8)) → base (w i)=[])
    (counter input reversed : List Bool) (accepted : Bool) (tail : List Bool)
    (limit : Nat) (bounded : input.length≤limit) :
    ∃ time ≤ counter.length*(20*limit+42)+1,
      Routine.Executes (listLoop extra w) (listState extra w base input reversed accepted tail counter) time
        (listState extra w base (scanItems counter.length input reversed accepted).suffix
          (scanItems counter.length input reversed accepted).reversed
          (scanItems counter.length input reversed accepted).accepted tail []) := by
  induction counter generalizing input reversed accepted with
  | nil =>
    have source : listState extra w base input reversed accepted tail [] (w 7)=[] := by simp [listState,w.injective.eq_iff]
    obtain ⟨ran,halted⟩ := Routine.repeat_empty (w 7) (listItem extra w) _ source
    exact ⟨1,by simp,⟨⟨1,_⟩,ran,halted,rfl⟩⟩
  | cons bit counter ih =>
    let start := listState extra w base input reversed accepted tail (bit::counter)
    let consumed := listState extra w base input reversed accepted tail counter
    have work (i : Fin 8) (member : i∈({1,2,4,5}:Finset (Fin 8))) : consumed (w i)=[] := by
      have not0 : i≠0 := by intro eq; subst i; exact (by decide : (0:Fin 8)∉({1,2,4,5}:Finset (Fin 8))) member
      have not3 : i≠3 := by intro eq; subst i; exact (by decide : (3:Fin 8)∉({1,2,4,5}:Finset (Fin 8))) member
      have not6 : i≠6 := by intro eq; subst i; exact (by decide : (6:Fin 8)∉({1,2,4,5}:Finset (Fin 8))) member
      have not7 : i≠7 := by intro eq; subst i; exact (by decide : (7:Fin 8)∉({1,2,4,5}:Finset (Fin 8))) member
      simpa only [consumed,listState,w.injective.eq_iff,if_neg not0,if_neg not3,if_neg not6,if_neg not7] using empty i member
    have status : consumed (w 3)=accepted::tail := by simp [consumed,listState,w.injective.eq_iff]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=listItem_executes extra w consumed accepted tail status
      (work 1 (by decide)) (work 2 (by decide)) (work 4 (by decide)) (work 5 (by decide))
    have source : start (w 7)=bit::counter := by simp [start,listState,w.injective.eq_iff]
    have changed : Function.update start (w 7) counter=consumed := listState_counter extra w base input reversed accepted tail _ _
    have firstRun := Routine.repeat_iteration (w 7) (listItem extra w) start bit counter source bodyTime finishBody
      (by simpa only [changed] using bodyRun) bodyHalt
    change Machine.run (step (listLoop extra w).program) (bodyTime+2)
      ⟨0,listState extra w base input reversed accepted tail (bit::counter)⟩ = some ⟨0,finishBody.store⟩ at firstRun
    have result : finishBody.store=listState extra w base (unframeSuffix input)
        ((Encoding.frame (unframePayload input)).reverse++reversed) (accepted && itemAccepted input) tail counter :=
      bodyStore.trans (listState_item extra w base input reversed accepted tail counter)
    have nextBound : (unframeSuffix input).length≤limit := (unframe_suffix_length input).trans bounded
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih (unframeSuffix input)
      ((Encoding.frame (unframePayload input)).reverse++reversed) (accepted && itemAccepted input) nextBound
    have bodyTimeBound : bodyTime≤20*limit+40 := by
      have source0 : consumed (w 0)=input := by simp [consumed,listState]
      rw [source0] at bodyBound
      omega
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,result]
      exact tailRun
    · exact tailStore

end Counting.StackMachine.EncodingPrograms
