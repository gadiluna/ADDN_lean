import Counting.ComplexityModel

namespace Counting.Machine

/-- Extra represented blank cells are genuinely empty tape, not work data. -/
theorem blank_list_denotes (count : Nat) :
    Turing.ListBlank.mk (List.replicate count Symbol.blank) = Turing.ListBlank.mk ([] : List Symbol) := by
  apply Turing.ListBlank.ext
  intro position
  simp only [Turing.ListBlank.nth_mk]
  by_cases inside : position < count
  · rw [List.getI_eq_getElem _ (by simpa using inside)]
    simp
    rfl
  · rw [List.getI_eq_default _ (by simpa using Nat.le_of_not_gt inside)]
    simp

/-- The incrementer restores the entire tape, including the left side.
Thus it is composable without an uncharged cleanup operation. -/
theorem increment_output_clean (bits : List Bool) :
    (rewindEnd ((increment bits).map bitSymbol)).tape.denotes =
      Turing.Tape.mk₁ ((increment bits).map bitSymbol) := by
  have nonempty : increment bits ≠ [] := by rw [increment_eq]; simp
  cases encoded : (increment bits).map bitSymbol with
  | nil => simp only [List.map_eq_nil_iff] at encoded; exact (nonempty encoded).elim
  | cons head tail =>
      have blank := blank_list_denotes 1
      change (⟨head, Turing.ListBlank.mk [.blank], Turing.ListBlank.mk tail⟩ : Turing.Tape Symbol) =
        ⟨head, Turing.ListBlank.mk [], Turing.ListBlank.mk tail⟩
      exact congrArg (fun left => (⟨head,left,Turing.ListBlank.mk tail⟩ : Turing.Tape Symbol)) blank

theorem increment_computesCleanIn :
    Complexity.ComputesCleanIn incrementProgram increment (Complexity.polynomial 3 1) := by
  intro input
  refine ⟨3*carryLength input+3, _, ?_, increment_halts input, increment_output_clean input⟩
  simpa only [Complexity.polynomial, pow_one, Nat.mul_add, Nat.mul_one] using increment_steps_le input

/-- Clean arithmetic on the actual little-endian natural payload. The
frame used by the `natural` codec is a separate, explicitly charged layer. -/
theorem increment_natural_clean (n : Nat) :
    ∃ steps output, steps ≤ 3*n.size+3 ∧ HaltsAt incrementProgram n.bits steps output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((n+1).bits.map bitSymbol) := by
  refine ⟨_, _, ?_, increment_halts n.bits, ?_⟩
  · simpa only [Encoding.bits_length] using increment_steps_le n.bits
  · rw [← increment_bits]
    exact increment_output_clean n.bits

end Counting.Machine
