import Counting.ComplexityModel

/-! Constant-step binary tape primitives. Right shift computes natural
division by two on canonical inputs; left shift prepends a zero bit. The
output convention is mathlib's inclusive right tape, so consumed input to
the left of the head is harmless and is not silently charged as erased. -/
namespace Counting.Machine

theorem Tape.ofWord_output (word : List Symbol) :
    (Tape.ofWord word).denotes.right₀ = Turing.ListBlank.mk word := by
  rw [Tape.denotes_ofWord]
  exact Turing.Tape.mk'_right₀ _ _

def rightShiftProgram : Program where
  states := 1
  code state _ := if state == 0 then some (1, .move .right) else none
  accept _ := true

def rightShiftEnd (input : List Bool) : Config rightShiftProgram :=
  ⟨1, (Tape.ofWord (input.map bitSymbol)).move .right⟩

theorem rightShift_halts (input : List Bool) :
    HaltsAt rightShiftProgram input 1 (rightShiftEnd input) := by
  constructor <;> rfl

theorem rightShift_output (input : List Bool) :
    (rightShiftEnd input).tape.denotes.right₀ = Turing.ListBlank.mk (input.tail.map bitSymbol) := by
  have same : (rightShiftEnd input).tape.denotes.right₀ =
      (Tape.ofWord (input.tail.map bitSymbol)).denotes.right₀ := by
    cases input <;> rfl
  rw [same, Tape.ofWord_output]

theorem rightShift_natural (n : Nat) :
    (rightShiftEnd n.bits).tape.denotes.right₀ = Turing.ListBlank.mk ((n / 2).bits.map bitSymbol) := by
  rw [rightShift_output, ← Nat.div2_bits_eq_tail, Nat.div2_val]

theorem rightShift_computesIn : Complexity.ComputesIn rightShiftProgram List.tail (fun _ => 1) := by
  intro input
  exact ⟨1, _, le_refl _, rightShift_halts input, rightShift_output input⟩

def leftShiftProgram : Program where
  states := 2
  code state _ := match state.val with
    | 0 => some (1, .move .left)
    | 1 => some (2, .write .zero)
    | _ => none
  accept _ := true

def leftShiftEnd (input : List Bool) : Config leftShiftProgram :=
  ⟨2, ((Tape.ofWord (input.map bitSymbol)).move .left).write .zero⟩

theorem leftShift_halts (input : List Bool) :
    HaltsAt leftShiftProgram input 2 (leftShiftEnd input) := by
  constructor <;> rfl

theorem leftShift_output (input : List Bool) :
    (leftShiftEnd input).tape.denotes.right₀ = Turing.ListBlank.mk ((false :: input).map bitSymbol) := by
  change (((Tape.ofWord (input.map bitSymbol)).move .left).write .zero).denotes.right₀ = _
  rw [Tape.denotes_write, Tape.denotes_move]
  change ((Tape.ofWord (input.map bitSymbol)).denotes.right₀).cons .zero = _
  rw [Tape.ofWord_output]
  rfl

theorem leftShift_value (input : List Bool) : Encoding.value (false :: input) = 2 * Encoding.value input := rfl

theorem leftShift_natural (n : Nat) (positive : n ≠ 0) :
    (leftShiftEnd n.bits).tape.denotes.right₀ = Turing.ListBlank.mk ((2 * n).bits.map bitSymbol) := by
  rw [leftShift_output, Nat.bit0_bits n positive]

theorem leftShift_computesIn : Complexity.ComputesIn leftShiftProgram (fun input => false :: input)
    (fun _ => 2) := by
  intro input
  exact ⟨2, _, le_refl _, leftShift_halts input, leftShift_output input⟩

end Counting.Machine
