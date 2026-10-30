import Counting.ComplexityModel

/-! A concrete finite-control parser for the self-delimiting frame prefix.
It accepts exactly inputs with a complete frame prefix, rejects truncated
ones, and uses at most one transition per input bit. -/
namespace Counting.Machine

def frameProgram : Program where
  states := 2
  code state symbol := match state.val, symbol with
    | 0, .one => some (1, .move .right)
    | 0, .zero => some (2, .write .zero)
    | 1, .one | 1, .zero => some (0, .move .right)
    | _, _ => none
  accept state := state == 2

def frameStart (left : List Symbol) (input : List Bool) : Config frameProgram :=
  ⟨0, ⟨left, (input.map bitSymbol).headD .blank, (input.map bitSymbol).tail⟩⟩

def frameScan (left : List Symbol) : List Bool → Nat × Config frameProgram
  | [] => (0, frameStart left [])
  | false :: rest => (1, ⟨2, ⟨left, .zero, rest.map bitSymbol⟩⟩)
  | [true] => (1, ⟨1, ⟨.one :: left, .blank, []⟩⟩)
  | true :: bit :: rest =>
      let result := frameScan (bitSymbol bit :: .one :: left) rest
      (result.1 + 2, result.2)

theorem frameScan_run (left : List Symbol) (input : List Bool) :
    run (step frameProgram) (frameScan left input).1 (frameStart left input) =
      some (frameScan left input).2 := by
  induction input using List.twoStepInduction generalizing left with
  | nil => rfl
  | singleton bit => cases bit <;> rfl
  | cons_cons flag bit rest ih _ =>
      cases flag with
      | false => rfl
      | true =>
          change run (step frameProgram) ((frameScan (bitSymbol bit :: .one :: left) rest).1 + 2)
            (frameStart left (true :: bit :: rest)) = _
          rw [Nat.add_comm _ 2, run_add]
          have first : run (step frameProgram) 2 (frameStart left (true :: bit :: rest)) =
              some (frameStart (bitSymbol bit :: .one :: left) rest) := by cases bit <;> rfl
          rw [first, Option.bind_some, ih]
          rfl

theorem frameScan_halted (left : List Symbol) (input : List Bool) :
    step frameProgram (frameScan left input).2 = none := by
  induction input using List.twoStepInduction generalizing left with
  | nil => rfl
  | singleton bit => cases bit <;> rfl
  | cons_cons flag bit rest ih _ => cases flag with
    | false => rfl
    | true => exact ih (bitSymbol bit :: .one :: left)

theorem frameScan_steps (left : List Symbol) (input : List Bool) :
    (frameScan left input).1 ≤ input.length := by
  induction input using List.twoStepInduction generalizing left with
  | nil => rfl
  | singleton bit => cases bit <;> simp [frameScan, frameProgram]
  | cons_cons flag bit rest ih _ => cases flag with
    | false => simp only [frameScan, List.length_cons]; omega
    | true =>
        have := ih (bitSymbol bit :: .one :: left)
        simp only [frameScan, List.length_cons]
        omega

theorem frameScan_accepts (left : List Symbol) (input : List Bool) :
    frameProgram.accept (frameScan left input).2.control = true ↔
      (Encoding.unframe input).isSome = true := by
  induction input using List.twoStepInduction generalizing left with
  | nil => simp [frameScan, frameStart, frameProgram, Encoding.unframe]
  | singleton bit => cases bit <;> simp [frameScan, frameProgram, Encoding.unframe]
  | cons_cons flag bit rest ih _ => cases flag with
    | false => simp [frameScan, frameProgram, Encoding.unframe]
    | true =>
        simpa only [frameScan, Encoding.unframe, Option.isSome_map] using
          ih (bitSymbol bit :: .one :: left)

theorem frame_halts (input : List Bool) :
    HaltsAt frameProgram input (frameScan [] input).1 (frameScan [] input).2 :=
  ⟨frameScan_run [] input, frameScan_halted [] input⟩

theorem frame_prefix_linear : Complexity.DecidesIn frameProgram
    {input | (Encoding.unframe input).isSome = true} (fun length => length) := by
  constructor
  · intro input
    exact ⟨_, _, frameScan_steps [] input, frame_halts input⟩
  · intro input
    rw [accepts_iff_of_halts (frame_halts input)]
    exact frameScan_accepts [] input

theorem frame_prefix_in_P : Complexity.P {input | (Encoding.unframe input).isSome = true} := by
  refine ⟨frameProgram, 1, 1, ?_, frame_prefix_linear.2⟩
  intro input
  refine ⟨_, _, ?_, frame_halts input⟩
  have := frameScan_steps [] input
  simpa only [Complexity.polynomial, pow_one, Nat.one_mul] using this.trans (Nat.le_succ _)

end Counting.Machine
