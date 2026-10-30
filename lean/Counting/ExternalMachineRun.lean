import Counting.ExternalMachineTape

namespace Counting.External.MachineBridge
open Machine

/-- A fixed-length tableau repeats an actual halted configuration. -/
def stutterRun (program : Program) : Nat → Machine.Config program → Machine.Config program
  | 0, config => config
  | time+1, config => stutter program (stutterRun program time config)

theorem stutterRun_succ_fromStart (program : Program) (time : Nat) (config : Machine.Config program) :
    stutterRun program (time+1) config = stutterRun program time (stutter program config) := by
  induction time with
  | zero => rfl
  | succ time ih => exact congrArg (stutter program) ih

theorem stutterRun_add (program : Program) (first second : Nat) (config : Machine.Config program) :
    stutterRun program (first+second) config = stutterRun program second (stutterRun program first config) := by
  induction second with
  | zero => rfl
  | succ second ih => exact congrArg (stutter program) ih

theorem stutterRun_of_none (program : Program) (time : Nat) (config : Machine.Config program)
    (halted : Machine.step program config = none) : stutterRun program time config = config := by
  induction time with
  | zero => rfl
  | succ time ih => simp only [stutterRun, ih, stutter, halted, Option.getD_none]

theorem stutterRun_of_run (program : Program) (time : Nat) (first last : Machine.Config program)
    (success : Machine.run (Machine.step program) time first = some last) :
    stutterRun program time first = last := by
  induction time generalizing first with
  | zero => exact Option.some.inj success
  | succ time ih =>
      cases instruction : Machine.step program first with
      | none => simp only [Machine.run, instruction, Option.bind_none] at success; contradiction
      | some next =>
          rw [stutterRun_succ_fromStart]
          simp only [stutter, instruction, Option.getD_some]
          apply ih next
          simpa only [Machine.run, instruction, Option.bind_some] using success

/-- Every padded run is an actual run of no more steps, and padding can
occur only after a genuine halt. -/
theorem stutterRun_reaches (program : Program) (time : Nat) (first : Machine.Config program) :
    ∃ steps ≤ time,
      Machine.run (Machine.step program) steps first = some (stutterRun program time first) ∧
      (steps = time ∨ Machine.step program (stutterRun program time first) = none) := by
  induction time with
  | zero => exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  | succ time ih =>
      obtain ⟨steps, bound, reached, terminal⟩ := ih
      cases instruction : Machine.step program (stutterRun program time first) with
      | none =>
          have fixed : stutterRun program (time+1) first = stutterRun program time first := by
            simp only [stutterRun, stutter, instruction, Option.getD_none]
          exact ⟨steps, by omega, by simpa only [fixed] using reached,
            Or.inr (by simpa only [fixed] using instruction)⟩
      | some next =>
          have count : steps = time := terminal.resolve_right (by rw [instruction]; simp)
          have fixed : stutterRun program (time+1) first = next := by
            simp only [stutterRun, stutter, instruction, Option.getD_some]
          refine ⟨steps+1, by omega, ?_, Or.inl (by omega)⟩
          rw [Machine.run_add, reached, Option.bind_some]
          simp only [Machine.run, instruction, Option.bind_some, fixed]

/-- Halting and acceptance at the last padded row are equivalent to actual
halting and acceptance within the unpadded step bound. -/
theorem stutterRun_accepts_iff (program : Program) (input : List Bool) (time : Nat) :
    (Machine.step program (stutterRun program time (Machine.initial program input)) = none ∧
      program.accept (stutterRun program time (Machine.initial program input)).control = true) ↔
      ∃ steps ≤ time, ∃ output,
        Machine.HaltsAt program input steps output ∧ program.accept output.control = true := by
  constructor
  · rintro ⟨halted, accepted⟩
    obtain ⟨steps, bound, reached, _⟩ := stutterRun_reaches program time (Machine.initial program input)
    exact ⟨steps, bound, _, ⟨reached, halted⟩, accepted⟩
  · rintro ⟨steps, bound, output, halted, accepted⟩
    have initialRun := stutterRun_of_run program steps _ _ halted.1
    have split : time = steps+(time-steps) := by omega
    have equal : stutterRun program time (Machine.initial program input) = output := by
      rw [split, stutterRun_add, initialRun, stutterRun_of_none program _ output halted.2]
    rw [equal]
    exact ⟨halted.2, accepted⟩

end Counting.External.MachineBridge
