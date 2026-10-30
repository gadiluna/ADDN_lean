import Counting.StackEncodingFlagged

namespace Counting.StackMachine.EncodingPrograms

def flaggedResult (extra : Nat) (source target temporary flag : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) : Fin (extra+4) → List Bool :=
  match Encoding.unframe (store source) with
  | none => Function.update (parserStore extra source target temporary store [] (store target) []) flag (false::store flag)
  | some (payload,suffix) => Function.update
      (parserStore extra source target temporary store suffix (payload++store target) []) flag (true::store flag)

theorem parserStore_update_work (extra : Nat) (source target temporary : Fin (extra+4))
    (sw : source≠temporary) (tw : target≠temporary)
    (store : Fin (extra+4) → List Bool) (input output old work : List Bool) :
    Function.update (parserStore extra source target temporary store input output old) temporary work =
      parserStore extra source target temporary store input output work := by
  funext r
  by_cases same : r=temporary
  · subst r; simp [parserStore, Ne.symm sw, Ne.symm tw]
  · simp only [Function.update_of_ne same, parserStore]
    split_ifs <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary-store contract for one frame. Successful parsing retains the
suffix; truncation consumes the input and leaves the target unchanged. Every
exit clears scratch and prepends its Boolean result to the flag register. -/
theorem flagged_run (extra : Nat) (source target temporary flag : Fin (extra+4))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (fs : flag≠source) (ft : flag≠target) (fw : flag≠temporary)
    (store : Fin (extra+4) → List Bool) (empty : store temporary=[]) :
    ∃ time ≤ 3*(store source).length+4,
      Machine.run (step (flaggedProgram extra source target temporary flag)) time ⟨0,store⟩ =
        some ⟨10,flaggedResult extra source target temporary flag store⟩ := by
  have start : flaggedEmbed extra source target temporary flag
      (unframeConfig (extra+1) source target temporary 0 store (store source) (store target) []) =
      (⟨0,store⟩ : Config (flaggedProgram extra source target temporary flag)) := by
    apply congrArg (Config.mk _)
    change parserStore extra source target temporary store (store source) (store target) [] = store
    rw [← empty, parserStore_initial]
  cases parsed : Encoding.unframe (store source) with
  | some pair =>
    obtain ⟨payload,suffix⟩ := pair
    have split := Machine.unframe_sound (store source) payload suffix parsed
    have executed := unframe_frames (extra+1) source target temporary st sw tw store payload suffix (store target)
    rw [← split] at executed
    have lifted := flagged_lift_run extra source target temporary flag _ _ _ executed
    rw [start] at lifted
    have flagvalue : parserStore extra source target temporary store suffix (payload++store target) [] flag = store flag :=
      parserStore_other extra source target temporary flag fs ft fw _ _ _ _
    refine ⟨5*payload.length+3, ?_, ?_⟩
    · rw [split, List.length_append, Encoding.frame_length]
      omega
    · rw [show 5*payload.length+3=(5*payload.length+2)+1 by omega, Machine.run_add, lifted, Option.bind_some]
      change Machine.run (step (flaggedProgram extra source target temporary flag)) 1
        ⟨7,parserStore extra source target temporary store suffix (payload++store target) []⟩ = _
      have emit := flagged_emit extra source target temporary flag
        (parserStore extra source target temporary store suffix (payload++store target) []) true
      simpa only [ite_true, flagvalue, flaggedResult, parsed] using emit
  | none =>
    obtain ⟨time,bounded,changed,size,executed⟩ := unframe_malformed_bounded (extra+1) source target temporary sw tw
      store (store source) (store target) [] parsed
    have lifted := flagged_lift_run extra source target temporary flag _ _ _ executed
    rw [start] at lifted
    let clean := parserStore extra source target temporary store [] (store target) []
    have clear := flagged_clear extra source target temporary flag clean changed
    dsimp only [clean] at clear
    rw [parserStore_update_work extra source target temporary sw tw] at clear
    rw [parserStore_update_work extra source target temporary sw tw] at clear
    have flagvalue : clean flag = store flag := parserStore_other extra source target temporary flag fs ft fw _ _ _ _
    refine ⟨time+(changed.length+1)+1, by simp only [List.length_nil, Nat.add_zero] at size; omega, ?_⟩
    rw [Machine.run_add, Machine.run_add, lifted, Option.bind_some]
    change (Machine.run (step (flaggedProgram extra source target temporary flag)) (changed.length+1)
      ⟨8,parserStore extra source target temporary store [] (store target) changed⟩).bind _ = _
    rw [clear, Option.bind_some]
    have emit := flagged_emit extra source target temporary flag clean false
    simpa only [Bool.false_eq_true, if_false, flagvalue, flaggedResult, parsed, clean] using emit

theorem flagged_halted (extra : Nat) (source target temporary flag : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) :
    step (flaggedProgram extra source target temporary flag) ⟨10,store⟩ = none := rfl

theorem flagged_executes (extra : Nat) (source target temporary flag : Fin (extra+4))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (fs : flag≠source) (ft : flag≠target) (fw : flag≠temporary)
    (store : Fin (extra+4) → List Bool) (empty : store temporary=[]) :
    ∃ time ≤ 3*(store source).length+4,
      Routine.Executes (Routine.ofProgram (flaggedProgram extra source target temporary flag)) store time
        (flaggedResult extra source target temporary flag store) := by
  obtain ⟨time,bounded,executed⟩ := flagged_run extra source target temporary flag st sw tw fs ft fw store empty
  exact ⟨time,bounded,⟨_,executed,flagged_halted _ _ _ _ _ _,rfl⟩⟩

theorem flagged_result_flag (extra : Nat) (source target temporary flag : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) :
    flaggedResult extra source target temporary flag store flag =
      (Encoding.unframe (store source)).isSome::store flag := by
  unfold flaggedResult
  cases parsed : Encoding.unframe (store source) with
  | none => simp
  | some pair => obtain ⟨payload,suffix⟩:=pair; simp

theorem flagged_result_scratch (extra : Nat) (source target temporary flag : Fin (extra+4))
    (sw : source≠temporary) (tw : target≠temporary) (fw : flag≠temporary)
    (store : Fin (extra+4) → List Bool) :
    flaggedResult extra source target temporary flag store temporary = [] := by
  unfold flaggedResult
  cases parsed : Encoding.unframe (store source) with
  | none => simp [parserStore, Ne.symm sw, Ne.symm tw, Ne.symm fw]
  | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore, Ne.symm sw, Ne.symm tw, Ne.symm fw]

end Counting.StackMachine.EncodingPrograms
