import Counting.StackEncodingUnframe

namespace Counting.StackMachine.EncodingPrograms

theorem unframe_empty_failure (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (output work : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) 1
      (unframeConfig extra source target temporary 0 base [] output work) =
      some (unframeConfig extra source target temporary 8 base [] output work) := by
  simp [Machine.run, step, unframeProgram, unframeConfig]
  rfl

theorem unframe_flag_failure (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (output work : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) 2
      (unframeConfig extra source target temporary 0 base [true] output work) =
      some (unframeConfig extra source target temporary 8 base [] output work) := by
  dsimp [Machine.run, step, unframeProgram, unframeConfig]
  simp
  refine ⟨rfl, ?_⟩
  funext r
  by_cases same : r=source
  · subst r; simp
  · simp [same]

/-- Truncation never runs the restoring phase, so the output register is
unchanged. Failure still halts within a linear bound on every binary input. -/
theorem unframe_malformed (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool)
    (invalid : Encoding.unframe input = none) :
    ∃ time ≤ 2*input.length+2, ∃ changed,
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
    obtain ⟨time, bounded, changed, executed⟩ := ih (bit::work) invalidTail
    refine ⟨3+time, by simp only [List.length_cons]; omega, changed, ?_⟩
    rw [Machine.run_add, unframe_bit extra source target temporary sw tw, Option.bind_some, executed]
  | case3 input nofalse notwo =>
    cases input with
    | nil => exact ⟨1, by simp, work, unframe_empty_failure _ _ _ _ _ _ _⟩
    | cons bit rest =>
      cases bit with
      | false => exact (nofalse rest rfl).elim
      | true =>
        cases rest with
        | nil => exact ⟨2, by simp, work, unframe_flag_failure _ _ _ _ _ _ _⟩
        | cons bit rest => exact (notwo bit rest rfl).elim

def unframePayload (input : List Bool) : List Bool :=
  ((Encoding.unframe input).map Prod.fst).getD []

theorem initial_eq_unframe (input : List Bool) :
    initial (unframeProgram 0 0 1 2) input = unframeConfig 0 0 1 2 0 (fun _ => []) input [] [] := by
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

/-- Total transduction, with the empty word as failure output. The generic
parser additionally exposes distinct success/failure controls and suffix. -/
theorem unframe_computes : ComputesIn (unframeProgram 0 0 1 2) unframePayload
    (fun length => 3*length+2) := by
  intro input
  cases parsed : Encoding.unframe input with
  | none =>
    obtain ⟨time, bounded, changed, executed⟩ :=
      unframe_malformed 0 0 1 2 (by decide) (by decide) (fun _ => []) input [] [] parsed
    refine ⟨time, unframeConfig 0 0 1 2 8 (fun _ => []) [] [] changed, by dsimp; omega,
      ⟨?_, (unframe_halted _ _ _ _ _ _ _ _).2⟩, ?_⟩
    · rw [initial_eq_unframe]
      exact executed
    · simp only [unframePayload, parsed]
      rfl
  | some pair =>
    obtain ⟨payload, suffix⟩ := pair
    have split := Machine.unframe_sound input payload suffix parsed
    have length : input.length = 2*payload.length+1+suffix.length := by
      rw [split, List.length_append, Encoding.frame_length]
    refine ⟨5*payload.length+2, unframeConfig 0 0 1 2 7 (fun _ => []) suffix payload [],
      by dsimp; omega, ⟨?_, (unframe_halted _ _ _ _ _ _ _ _).1⟩, ?_⟩
    · rw [initial_eq_unframe, split]
      simpa only [List.append_nil] using
        unframe_frames 0 0 1 2 (by decide) (by decide) (by decide) (fun _ => []) payload suffix []
    · simp only [unframePayload, parsed]
      rfl

theorem unframe_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile (unframeProgram 0 0 1 2)) unframePayload
      (Complexity.polynomial (20*(3+1+5)^2) 4) := by
  apply Compiler.computesCleanIn_polynomial 3 1
  intro input
  obtain ⟨time, output, bound, halted, value⟩ := unframe_computes input
  refine ⟨time, output, ?_, halted, value⟩
  simp only [Complexity.polynomial, pow_one]
  dsimp only at bound
  omega

end Counting.StackMachine.EncodingPrograms
