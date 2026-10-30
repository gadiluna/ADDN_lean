import Counting.MachineModel
import Counting.EncodingBinary

/-! A concrete four-state binary increment machine. The input and output
are little-endian bit strings. The head returns to the first output bit.
Its cost counts actual writes and moves in `MachineModel`. -/
namespace Counting.Machine

def increment : List Bool → List Bool
  | [] => [true]
  | false :: tail => true :: tail
  | true :: tail => false :: increment tail

def carryLength : List Bool → Nat
  | true :: tail => carryLength tail + 1
  | _ => 0

def carrySuffix : List Bool → List Bool
  | true :: tail => carrySuffix tail
  | false :: tail => tail
  | [] => []

theorem increment_eq (bits : List Bool) :
    increment bits = List.replicate (carryLength bits) false ++ true :: carrySuffix bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [increment, carryLength, carrySuffix, ih, List.replicate_succ]

theorem increment_value (bits : List Bool) : Encoding.value (increment bits) = Encoding.value bits + 1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> simp only [increment, Encoding.value, Nat.bit_val, Bool.toNat_false,
        Bool.toNat_true] at *
      omega

theorem increment_bits (n : Nat) : increment n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit bit n admissible ih =>
      rw [Nat.bits_append_bit n bit admissible]
      cases bit with
      | false => simpa only [increment, Nat.bit_false] using (Nat.bit1_bits n).symm
      | true =>
          rw [increment, ih]
          have arithmetic : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
          rw [arithmetic, Nat.bit0_bits (n + 1) (by omega)]

theorem carryLength_le (bits : List Bool) : carryLength bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp only [carryLength, List.length_cons] <;> omega

def incrementProgram : Program where
  states := 3
  code state symbol :=
    match state.val, symbol with
    | 0, .one => some (1, .write .zero)
    | 0, .zero | 0, .blank => some (2, .write .one)
    | 1, _ => some (0, .move .right)
    | 2, .zero | 2, .one => some (2, .move .left)
    | 2, .blank => some (3, .move .right)
    | _, _ => none
  accept state := state == 3

def carryStart (left : List Symbol) (bits : List Bool) : Config incrementProgram :=
  ⟨0, ⟨left, (bits.map bitSymbol).headD .blank, (bits.map bitSymbol).tail⟩⟩

def carryEnd (left : List Symbol) (bits : List Bool) : Config incrementProgram :=
  ⟨2, ⟨List.replicate (carryLength bits) .zero ++ left, .one, (carrySuffix bits).map bitSymbol⟩⟩

theorem carry_run (left : List Symbol) (bits : List Bool) :
    run (step incrementProgram) (2 * carryLength bits + 1) (carryStart left bits) =
      some (carryEnd left bits) := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit bits ih =>
      cases bit with
      | false => rfl
      | true =>
          rw [show 2 * carryLength (true :: bits) + 1 = 2 + (2 * carryLength bits + 1) by
            simp only [carryLength]; omega, run_add]
          have first : run (step incrementProgram) 2 (carryStart left (true :: bits)) =
              some (carryStart (.zero :: left) bits) := by rfl
          rw [first, Option.bind_some, ih]
          simp only [carryEnd, carryLength, carrySuffix, List.replicate_succ', List.append_assoc,
            List.singleton_append]

def rewindStart (left : List Bool) (head : Bool) (right : List Symbol) : Config incrementProgram :=
  ⟨2, ⟨left.map bitSymbol, bitSymbol head, right⟩⟩

def rewindEnd (word : List Symbol) : Config incrementProgram :=
  ⟨3, ⟨[.blank], word.headD .blank, word.tail⟩⟩

theorem rewind_run (left : List Bool) (head : Bool) (right : List Symbol) :
    run (step incrementProgram) (left.length + 2) (rewindStart left head right) =
      some (rewindEnd (left.reverse.map bitSymbol ++ bitSymbol head :: right)) := by
  induction left generalizing head right with
  | nil => cases head <;> rfl
  | cons bit tail ih =>
      rw [show (bit :: tail).length + 2 = (tail.length + 2) + 1 by simp only [List.length_cons]]
      have first : step incrementProgram (rewindStart (bit :: tail) head right) =
          some (rewindStart tail bit (bitSymbol head :: right)) := by cases head <;> rfl
      rw [run, first, Option.bind_some, ih]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append]

theorem increment_run (bits : List Bool) :
    run (step incrementProgram) (3 * carryLength bits + 3) (initial incrementProgram bits) =
      some (rewindEnd ((increment bits).map bitSymbol)) := by
  rw [show 3 * carryLength bits + 3 = (2 * carryLength bits + 1) + (carryLength bits + 2) by omega,
    run_add]
  change (run (step incrementProgram) (2 * carryLength bits + 1) (carryStart [] bits)).bind _ = _
  rw [carry_run, Option.bind_some]
  have carry : carryEnd [] bits = rewindStart (List.replicate (carryLength bits) false) true
      ((carrySuffix bits).map bitSymbol) := by
    simp only [carryEnd, rewindStart, List.map_replicate, bitSymbol, Bool.false_eq_true,
      if_false, if_true, List.append_nil]
  rw [carry]
  simpa only [List.length_replicate, List.reverse_replicate, List.map_replicate, increment_eq,
    List.map_append, List.map_cons] using
    rewind_run (List.replicate (carryLength bits) false) true ((carrySuffix bits).map bitSymbol)

theorem increment_halts (bits : List Bool) :
    HaltsAt incrementProgram bits (3 * carryLength bits + 3)
      (rewindEnd ((increment bits).map bitSymbol)) := by
  exact ⟨increment_run bits, rfl⟩

theorem increment_steps_le (bits : List Bool) : 3 * carryLength bits + 3 ≤ 3 * bits.length + 3 := by
  have := carryLength_le bits
  omega

theorem increment_output (bits : List Bool) :
    (rewindEnd ((increment bits).map bitSymbol)).tape.denotes.right₀ =
      Turing.ListBlank.mk ((increment bits).map bitSymbol) := by
  have nonempty : increment bits ≠ [] := by rw [increment_eq]; simp
  cases equal : (increment bits).map bitSymbol with
  | nil => simp only [List.map_eq_nil_iff] at equal; exact (nonempty equal).elim
  | cons head tail => rfl

/-- A genuine linear-time transduction in the fixed Turing model. The
theorem supplies its halted run, tape output and decoded arithmetic result. -/
theorem increment_binary_correct (n : Nat) :
    ∃ steps output, steps ≤ 3 * n.size + 3 ∧ HaltsAt incrementProgram n.bits steps output ∧
      output.tape.denotes.right₀ = Turing.ListBlank.mk ((increment n.bits).map bitSymbol) ∧
      Encoding.value (increment n.bits) = n + 1 := by
  refine ⟨_, _, ?_, increment_halts n.bits, increment_output n.bits, ?_⟩
  · simpa only [Encoding.bits_length] using increment_steps_le n.bits
  · rw [increment_value, Encoding.value_bits]

end Counting.Machine
