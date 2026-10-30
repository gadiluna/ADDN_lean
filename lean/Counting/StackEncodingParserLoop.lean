import Counting.StackEncodingParserMany

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

theorem parseStore_update_other {registers : Nat} (source status output counter : Fin (registers+2))
    (cs : counter≠source) (ct : counter≠status) (co : counter≠output)
    (store : Routine.Store registers) (accepted : Bool) (tail bits : List Bool) (result : ParseEffect) :
    Function.update (parseStore source status output store accepted tail result) counter bits=
      parseStore source status output (Function.update store counter bits) accepted tail result := by
  funext r
  by_cases a : r=counter
  · subst r; simp [parseStore,cs,ct,co]
  · simp [parseStore,a,Ne.symm co]

namespace VerifiedParser

/-- An enclosing list may keep its live counter outside the child's scratch.
The body is executed once per actual unary bit, including rejection paths. -/
theorem loop_executes {registers : Nat} {source status output : Fin (registers+2)}
    (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser registers source status output α codec)
    (counter : Fin (registers+2)) (cs : counter≠source) (ct : counter≠status) (co : counter≠output)
    (unused : counter∉parser.work)
    (bits : List Bool) (store : Routine.Store registers) (accepted : Bool) (tail : List Bool)
    (statusEq : store status=accepted::tail) (workEmpty : ∀ r∈parser.work,store r=[])
    (counterEq : store counter=bits) (limit : Nat) (inputBound : (store source).length≤limit) :
    ∃ time ≤ bits.length*(Complexity.polynomial parser.coefficient parser.exponent limit+2)+1,
      Routine.Executes (Routine.forEach counter parser.routine) store time
        (parseStore source status output (Function.update store counter []) accepted tail
          (manyEffect parser.effect bits.length (store source))) := by
  induction bits generalizing store accepted with
  | nil =>
    have unchanged : parseStore source status output (Function.update store counter []) accepted tail
        (manyEffect parser.effect 0 (store source))=store := by
      rw [←counterEq,Function.update_eq_self]
      funext r
      by_cases a : r=source
      · subst r; simp [parseStore,manyEffect]
      · by_cases b : r=status
        · subst r; simp [parseStore,manyEffect,Ne.symm ss,statusEq]
        · by_cases c : r=output
          · subst r; simp [parseStore,manyEffect,Ne.symm so,Ne.symm statusOutput]
          · simp [parseStore,a,b,c]
    obtain ⟨ran,halted⟩:=Routine.repeat_empty counter parser.routine store counterEq
    refine ⟨1,by simp,⟨⟨1,store⟩,ran,halted,?_⟩⟩
    exact unchanged.symm
  | cons bit bits ih =>
    let consumed := Function.update store counter bits
    have consumedSource : consumed source=store source := by simp [consumed,Ne.symm cs]
    have consumedStatus : consumed status=accepted::tail := by simp [consumed,Ne.symm ct,statusEq]
    have consumedEmpty (r : Fin (registers+2)) (member : r∈parser.work) : consumed r=[] := by
      have different : r≠counter := fun same => unused (same ▸ member)
      simpa only [consumed,Function.update_of_ne different] using workEmpty r member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=parser.executes consumed accepted tail consumedStatus consumedEmpty
    rw [consumedSource] at bodyBound bodyStore
    let middle := parseStore source status output consumed accepted tail (parser.effect (store source))
    have nextSource : middle source=(parser.effect (store source)).suffix := by simp [middle,parseStore]
    have nextStatus : middle status=(accepted && (parser.effect (store source)).accepted)::tail := by simp [middle,parseStore,Ne.symm ss]
    have nextCounter : middle counter=bits := by simp [middle,parseStore,cs,ct,co,consumed]
    have nextEmpty (r : Fin (registers+2)) (member : r∈parser.work) : middle r=[] := by
      exact (parser.scratch_unchanged consumed accepted tail (parser.effect (store source)) r member).trans (consumedEmpty r member)
    have nextBound : (middle source).length≤limit := by rw [nextSource]; exact (parser.suffix_le _).trans inputBound
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle
      (accepted && (parser.effect (store source)).accepted) nextStatus nextEmpty nextCounter nextBound
    have firstRun := Routine.repeat_iteration counter parser.routine store bit bits counterEq bodyTime finishBody bodyRun bodyHalt
    have bodyLimit : bodyTime≤Complexity.polynomial parser.coefficient parser.exponent limit := by
      apply bodyBound.trans
      unfold Complexity.polynomial
      gcongr
    have combinedStore :
        parseStore source status output (Function.update middle counter [])
          (accepted && (parser.effect (store source)).accepted) tail
          (manyEffect parser.effect bits.length (middle source)) =
        parseStore source status output (Function.update store counter []) accepted tail
          (manyEffect parser.effect (bit::bits).length (store source)) := by
      rw [nextSource]
      change parseStore source status output
        (Function.update (parseStore source status output consumed accepted tail (parser.effect (store source))) counter [])
        _ _ _ = _
      rw [parseStore_update_other source status output counter cs ct co,
        parseStore_product source status output ss so statusOutput]
      simp only [consumed,Function.update_idem,List.length_cons,manyEffect,productEffect]
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,tailStore.trans combinedStore⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
