import Counting.ComplexityModel

/-! The tape representation cannot create more than one represented cell
per primitive transition. A binary output has no blank symbols, so its
length is bounded by the represented tape span, independently of padding. -/
namespace Counting.Machine

def Tape.span (tape : Tape) : Nat := tape.left.length + 1 + tape.right.length

theorem Tape.write_span (tape : Tape) (symbol : Symbol) : (tape.write symbol).span = tape.span := rfl

theorem Tape.move_span (tape : Tape) (direction : Turing.Dir) :
    (tape.move direction).span ≤ tape.span + 1 := by
  cases direction <;> cases tape with
  | mk left head right =>
      cases left <;> cases right <;> simp [Tape.move, Tape.span] <;> omega

theorem step_span {program : Program} {first second : Config program}
    (success : step program first = some second) : second.tape.span ≤ first.tape.span + 1 := by
  unfold step at success
  obtain ⟨pair, _, equal⟩ := Option.map_eq_some_iff.mp success
  rcases pair with ⟨control, action⟩
  subst second
  cases action with
  | move direction => exact first.tape.move_span direction
  | write symbol => simp only [Tape.write_span]; omega

theorem run_span {program : Program} (steps : Nat) {first second : Config program}
    (success : run (step program) steps first = some second) :
    second.tape.span ≤ first.tape.span + steps := by
  induction steps generalizing first with
  | zero => have equal := Option.some.inj success; subst second; omega
  | succ steps ih =>
      cases next : step program first with
      | none => simp only [run, next, Option.bind_none] at success; contradiction
      | some middle =>
          have rest : run (step program) steps middle = some second := by
            simpa only [run, next, Option.bind_some] using success
          have firstBound := step_span next
          have restBound := ih rest
          omega

theorem initial_span (program : Program) (input : List Bool) :
    (initial program input).tape.span ≤ input.length + 1 := by
  cases input <;> simp [initial, Tape.ofWord, Tape.span]
  omega

theorem run_input_span {program : Program} {input : List Bool} {steps : Nat} {output : Config program}
    (halted : HaltsAt program input steps output) : output.tape.span ≤ input.length + steps + 1 := by
  have first := initial_span program input
  have bound := run_span steps halted.1
  omega

theorem binary_length_le_representation (symbols : List Symbol) (bits : List Bool)
    (same : Turing.ListBlank.mk symbols = Turing.ListBlank.mk (bits.map bitSymbol)) :
    bits.length ≤ symbols.length := by
  by_contra tooLong
  have inside : symbols.length < (bits.map bitSymbol).length := by
    simp only [List.length_map]
    omega
  have equal := congrArg (fun tape : Turing.ListBlank Symbol => tape.nth symbols.length) same
  simp only [Turing.ListBlank.nth_mk, List.getI_eq_default symbols (Nat.le_refl _),
    List.getI_eq_getElem _ inside, List.getElem_map] at equal
  exact bitSymbol_ne_blank _ equal.symm

theorem output_length_le_span (tape : Tape) (bits : List Bool)
    (output : tape.denotes.right₀ = Turing.ListBlank.mk (bits.map bitSymbol)) :
    bits.length ≤ tape.span := by
  have bound := binary_length_le_representation (tape.head :: tape.right) bits output
  simp only [List.length_cons] at bound
  unfold Tape.span
  omega

theorem output_length_le_steps {program : Program} {input outputBits : List Bool} {steps : Nat}
    {output : Config program} (halted : HaltsAt program input steps output)
    (tape : output.tape.denotes.right₀ = Turing.ListBlank.mk (outputBits.map bitSymbol)) :
    outputBits.length ≤ input.length + steps + 1 :=
  (output_length_le_span output.tape outputBits tape).trans (run_input_span halted)

theorem run_transport (program : Program) (steps : Nat) (first other final : Config program)
    (same : first.denotes = other.denotes)
    (success : run (step program) steps first = some final) :
    ∃ output, run (step program) steps other = some output ∧ output.denotes = final.denotes := by
  have known := run_simulates program steps first
  rw [success, same, Option.map_some] at known
  have transported := run_simulates program steps other
  rw [← known] at transported
  exact Option.map_eq_some_iff.mp transported

theorem halt_transport {program : Program} {first other : Config program}
    (same : first.denotes = other.denotes) (halted : step program first = none) :
    step program other = none := by
  have known := step_simulates program first
  rw [halted, same, Option.map_none] at known
  have transported := step_simulates program other
  rw [← known] at transported
  exact Option.map_eq_none_iff.mp transported

end Counting.Machine

namespace Counting.Complexity

theorem ComputesIn.output_length {program : Machine.Program} {function : Word → Word} {bound : Nat → Nat}
    (computes : ComputesIn program function bound) (input : Word) :
    (function input).length ≤ input.length + bound input.length + 1 := by
  obtain ⟨steps, output, cost, halted, tape⟩ := computes input
  have length := Machine.output_length_le_steps halted tape
  omega

theorem ComputesCleanIn.output_length {program : Machine.Program} {function : Word → Word} {bound : Nat → Nat}
    (computes : ComputesCleanIn program function bound) (input : Word) :
    (function input).length ≤ input.length + bound input.length + 1 :=
  computes.toComputesIn.output_length input

end Counting.Complexity
