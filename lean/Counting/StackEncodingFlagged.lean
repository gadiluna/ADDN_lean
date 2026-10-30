import Counting.StackEncodingNatural

/-! A compositional frame parser with an explicit success bit. Both exits
clear the temporary register; the suffix is retained on success. -/
namespace Counting.StackMachine.EncodingPrograms

def flaggedProgram (extra : Nat) (source target temporary flag : Fin (extra+4)) : Program where
  extraRegisters := extra+2
  states := 10
  code control := match control.val with
    | 0 => .pop source 8 4 1
    | 1 => .pop source 8 2 3
    | 2 => .push temporary false 0
    | 3 => .push temporary true 0
    | 4 => .pop temporary 7 5 6
    | 5 => .push target false 4
    | 6 => .push target true 4
    | 7 => .push flag true 10
    | 8 => .pop temporary 9 8 8
    | 9 => .push flag false 10
    | _ => .halt

def flaggedControl (extra : Nat) (source target temporary flag : Fin (extra+4))
    (control : Control (unframeProgram (extra+1) source target temporary)) :
    Control (flaggedProgram extra source target temporary flag) := ⟨control.val, by have:=control.isLt; change control.val<9 at this; change control.val<11; omega⟩

def flaggedEmbed (extra : Nat) (source target temporary flag : Fin (extra+4))
    (config : Config (unframeProgram (extra+1) source target temporary)) :
    Config (flaggedProgram extra source target temporary flag) :=
  ⟨flaggedControl extra source target temporary flag config.control, config.store⟩

theorem flagged_step (extra : Nat) (source target temporary flag : Fin (extra+4))
    (config next : Config (unframeProgram (extra+1) source target temporary))
    (success : step (unframeProgram (extra+1) source target temporary) config = some next) :
    step (flaggedProgram extra source target temporary flag) (flaggedEmbed extra source target temporary flag config) =
      some (flaggedEmbed extra source target temporary flag next) := by
  have code : (flaggedProgram extra source target temporary flag).code
      (flaggedControl extra source target temporary flag config.control) =
      ((unframeProgram (extra+1) source target temporary).code config.control).relabel
        (flaggedControl extra source target temporary flag) := by
    have nonhalt : (unframeProgram (extra+1) source target temporary).code config.control ≠ .halt := by
      intro equal
      simp only [step, equal] at success
      contradiction
    generalize equal : config.control = ctrl at nonhalt ⊢
    fin_cases ctrl <;> simp_all [unframeProgram] <;> rfl
  unfold step at success ⊢
  dsimp only [flaggedEmbed]
  rw [code]
  cases instruction : (unframeProgram (extra+1) source target temporary).code config.control with
  | halt => simp [instruction] at success
  | jump label =>
    simp only [instruction, Option.some.injEq] at success
    subst next
    rfl
  | push register bit label =>
    simp only [instruction, Option.some.injEq] at success
    subst next
    rfl
  | pop register empty zero one =>
    cases contents : config.store register with
    | nil =>
      simp only [instruction, contents, Option.some.injEq] at success
      subst next
      simp only [Instruction.relabel, contents]
    | cons bit rest =>
      simp only [instruction, contents, Option.some.injEq] at success
      subst next
      cases bit <;> simp only [Instruction.relabel, contents, ite_true, Bool.false_eq_true, if_false] <;> rfl

theorem flagged_lift_run (extra : Nat) (source target temporary flag : Fin (extra+4))
    (time : Nat) (start finish : Config (unframeProgram (extra+1) source target temporary))
    (executed : Machine.run (step (unframeProgram (extra+1) source target temporary)) time start = some finish) :
    Machine.run (step (flaggedProgram extra source target temporary flag)) time
      (flaggedEmbed extra source target temporary flag start) =
      some (flaggedEmbed extra source target temporary flag finish) := by
  induction time generalizing start with
  | zero => have equal:=Option.some.inj executed; subst finish; rfl
  | succ time ih =>
    cases next : step (unframeProgram (extra+1) source target temporary) start with
    | none => simp only [Machine.run, next, Option.bind_none] at executed; contradiction
    | some middle =>
      have tail : Machine.run (step (unframeProgram (extra+1) source target temporary)) time middle = some finish := by
        simpa only [Machine.run, next, Option.bind_some] using executed
      rw [Machine.run, flagged_step extra source target temporary flag start middle next, Option.bind_some]
      exact ih middle tail

def parserStore (extra : Nat) (source target temporary : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) (input output work : List Bool) : Fin (extra+4) → List Bool :=
  fun r => if r=source then input else if r=target then output else if r=temporary then work else store r

theorem parserStore_initial (extra : Nat) (source target temporary : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) :
    parserStore extra source target temporary store (store source) (store target) (store temporary) = store := by
  funext r
  simp only [parserStore]
  split_ifs with first second third
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · rfl

theorem parserStore_other (extra : Nat) (source target temporary r : Fin (extra+4))
    (rs : r≠source) (rt : r≠target) (rw : r≠temporary)
    (store : Fin (extra+4) → List Bool) (input output work : List Bool) :
    parserStore extra source target temporary store input output work r = store r := by
  simp only [parserStore, if_neg rs, if_neg rt, if_neg rw]

theorem flagged_emit (extra : Nat) (source target temporary flag : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) (result : Bool) :
    Machine.run (step (flaggedProgram extra source target temporary flag)) 1
      ⟨if result then 7 else 9, store⟩ =
      some ⟨10, Function.update store flag (result::store flag)⟩ := by
  cases result <;> rfl

theorem flagged_clear (extra : Nat) (source target temporary flag : Fin (extra+4))
    (store : Fin (extra+4) → List Bool) (work : List Bool) :
    Machine.run (step (flaggedProgram extra source target temporary flag)) (work.length+1)
      ⟨8, Function.update store temporary work⟩ =
      some ⟨9, Function.update store temporary []⟩ := by
  induction work with
  | nil => simp [Machine.run, step, flaggedProgram]; rfl
  | cons bit work ih =>
    rw [List.length_cons, show work.length+1+1=1+(work.length+1) by omega, Machine.run_add]
    have first : Machine.run (step (flaggedProgram extra source target temporary flag)) 1
        ⟨8, Function.update store temporary (bit::work)⟩ =
        some ⟨8, Function.update store temporary work⟩ := by
      cases bit <;> simp [Machine.run, step, flaggedProgram, Function.update_idem] <;> rfl
    rw [first, Option.bind_some]
    exact ih

/-- The failure workspace contains at most one bit for each consumed payload
bit, a bound used to charge its explicit clearing loop. -/
theorem unframe_malformed_bounded (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool)
    (invalid : Encoding.unframe input = none) :
    ∃ time ≤ 2*input.length+2, ∃ changed, changed.length ≤ input.length+work.length ∧
      Machine.run (step (unframeProgram extra source target temporary)) time
        (unframeConfig extra source target temporary 0 base input output work) =
        some (unframeConfig extra source target temporary 8 base [] output changed) := by
  induction input using Encoding.unframe.induct generalizing work with
  | case1 rest => simp [Encoding.unframe] at invalid
  | case2 bit input ih =>
    have invalidTail : Encoding.unframe input = none := by
      cases parsed : Encoding.unframe input with
      | none => rfl
      | some value => simp [Encoding.unframe, parsed] at invalid
    obtain ⟨time, bounded, changed, size, executed⟩ := ih (bit::work) invalidTail
    refine ⟨3+time, by simp only [List.length_cons]; omega, changed, ?_, ?_⟩
    · simp only [List.length_cons] at *; omega
    · rw [Machine.run_add, unframe_bit extra source target temporary sw tw, Option.bind_some, executed]
  | case3 input nofalse notwo =>
    cases input with
    | nil => exact ⟨1, by simp, work, by simp, unframe_empty_failure _ _ _ _ _ _ _⟩
    | cons bit rest =>
      cases bit with
      | false => exact (nofalse rest rfl).elim
      | true =>
        cases rest with
        | nil => exact ⟨2, by simp, work, by simp, unframe_flag_failure _ _ _ _ _ _ _⟩
        | cons bit rest => exact (notwo bit rest rfl).elim

end Counting.StackMachine.EncodingPrograms
