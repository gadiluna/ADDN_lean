import Counting.MachineArithmeticClean

namespace Counting.Machine

/-- Comparison state after processing lower-significance columns. -/
def compareColumn (previous a b : Bool) : Bool := if a = b then previous else !a

/-- Alternating little-endian operands, with a missing last bit interpreted
as zero. This total function also specifies odd-length binary inputs. -/
def compareColumns (previous : Bool) : List Bool → Bool
  | [] => previous
  | [a] => compareColumn previous a false
  | a::b::rest => compareColumns (compareColumn previous a b) rest

def evenBits : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | a::_::rest => a::evenBits rest

def oddBits : List Bool → List Bool
  | [] => []
  | [_] => []
  | _::b::rest => b::oddBits rest

theorem compareColumns_correct (previous : Bool) (input : List Bool) :
    compareColumns previous input = true ↔
      Encoding.value (evenBits input) < Encoding.value (oddBits input) ∨
      (Encoding.value (evenBits input) = Encoding.value (oddBits input) ∧ previous = true) := by
  induction input using List.twoStepInduction generalizing previous with
  | nil => simp [compareColumns, evenBits, oddBits, Encoding.value]
  | singleton a =>
      cases a <;> cases previous <;> simp [compareColumns, compareColumn, evenBits, oddBits, Encoding.value]
  | cons_cons a b rest ih _ =>
      rw [compareColumns, ih]
      cases a <;> cases b <;> cases previous <;>
        simp [compareColumn, evenBits, oddBits, Encoding.value, Nat.bit_val] <;> omega

theorem compareColumns_le (input : List Bool) :
    compareColumns true input = true ↔ Encoding.value (evenBits input) ≤ Encoding.value (oddBits input) := by
  rw [compareColumns_correct]
  simp only [and_true]
  omega

/-- Thirteen concrete finite-control states. Each input bit is erased in
one write and crossed in one move; the answer is written at the first
blank cell. Erasure is part of the measured computation. -/
def comparisonProgram : Program where
  states := 12
  code state symbol := match state.val, symbol with
    | 0, .zero => some (2, .write .blank)
    | 0, .one => some (3, .write .blank)
    | 0, .blank => some (12, .write .one)
    | 1, .zero => some (4, .write .blank)
    | 1, .one => some (5, .write .blank)
    | 1, .blank => some (12, .write .zero)
    | 2, _ => some (6, .move .right)
    | 3, _ => some (7, .move .right)
    | 4, _ => some (8, .move .right)
    | 5, _ => some (9, .move .right)
    | 6, .zero | 6, .one => some (10, .write .blank)
    | 6, .blank => some (12, .write .one)
    | 7, .zero => some (11, .write .blank)
    | 7, .one => some (10, .write .blank)
    | 7, .blank => some (12, .write .zero)
    | 8, .zero => some (11, .write .blank)
    | 8, .one => some (10, .write .blank)
    | 8, .blank => some (12, .write .zero)
    | 9, .zero | 9, .one => some (11, .write .blank)
    | 9, .blank => some (12, .write .zero)
    | 10, _ => some (0, .move .right)
    | 11, _ => some (1, .move .right)
    | _, _ => none
  accept state := state == 12

def compareStart (previous : Bool) (left : List Symbol) (input : List Bool) : Config comparisonProgram :=
  ⟨if previous then 0 else 1, ⟨left, (input.map bitSymbol).headD .blank, (input.map bitSymbol).tail⟩⟩

def compareEnd (previous : Bool) (left : List Symbol) (input : List Bool) : Config comparisonProgram :=
  ⟨12, ⟨List.replicate input.length .blank ++ left, bitSymbol (compareColumns previous input), []⟩⟩

theorem comparison_scan (previous : Bool) (left : List Symbol) (input : List Bool) :
    run (step comparisonProgram) (2*input.length+1) (compareStart previous left input) =
      some (compareEnd previous left input) := by
  induction input using List.twoStepInduction generalizing previous left with
  | nil => cases previous <;> rfl
  | singleton a => cases previous <;> cases a <;> rfl
  | cons_cons a b rest ih _ =>
      have time : 2*(a::b::rest).length+1 = 4+(2*rest.length+1) := by simp only [List.length_cons]; omega
      rw [time, run_add]
      have first : run (step comparisonProgram) 4 (compareStart previous left (a::b::rest)) =
          some (compareStart (compareColumn previous a b) (.blank::.blank::left) rest) := by
        cases previous <;> cases a <;> cases b <;> rfl
      rw [first, Option.bind_some, ih]
      simp only [compareEnd, compareColumns, List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append]
      rfl

theorem comparison_halts (input : List Bool) :
    HaltsAt comparisonProgram input (2*input.length+1) (compareEnd true [] input) :=
  ⟨comparison_scan true [] input, rfl⟩

theorem comparison_clean (input : List Bool) :
    (compareEnd true [] input).tape.denotes =
      Turing.Tape.mk₁ ((Encoding.boolean.encode (compareColumns true input)).map bitSymbol) := by
  change (⟨bitSymbol (compareColumns true input),
    Turing.ListBlank.mk (List.replicate input.length .blank ++ []),
    Turing.ListBlank.mk []⟩ : Turing.Tape Symbol) =
    ⟨bitSymbol (compareColumns true input), Turing.ListBlank.mk [], Turing.ListBlank.mk []⟩
  rw [List.append_nil, blank_list_denotes]

theorem comparison_computesCleanIn :
    Complexity.ComputesCleanIn comparisonProgram
      (fun input => Encoding.boolean.encode (compareColumns true input))
      (fun length => 2*length+1) := by
  intro input
  exact ⟨_, _, le_rfl, comparison_halts input, comparison_clean input⟩

/-- Binary columns are only a tape layout. Conversion from the repository's
sequential natural-pair codec requires its own machine and is not free. -/
def interleave : List Bool → List Bool → List Bool
  | [], [] => []
  | a::first, [] => a::false::interleave first []
  | [], b::second => false::b::interleave [] second
  | a::first, b::second => a::b::interleave first second

theorem interleave_values (first second : List Bool) :
    Encoding.value (evenBits (interleave first second)) = Encoding.value first ∧
      Encoding.value (oddBits (interleave first second)) = Encoding.value second := by
  induction first generalizing second with
  | nil =>
      induction second with
      | nil => simp [interleave, evenBits, oddBits, Encoding.value]
      | cons b second ih =>
          simp [interleave, evenBits, oddBits, Encoding.value, ih.1, ih.2]
  | cons a first ih =>
      cases second with
      | nil =>
          obtain ⟨left,right⟩ := ih []
          simp [interleave, evenBits, oddBits, Encoding.value, left, right]
      | cons b second =>
          obtain ⟨left,right⟩ := ih second
          simp [interleave, evenBits, oddBits, Encoding.value, left, right]

theorem comparison_natural (first second : Nat) :
    compareColumns true (interleave first.bits second.bits) = decide (first ≤ second) := by
  apply Bool.eq_iff_iff.mpr
  rw [compareColumns_le, (interleave_values first.bits second.bits).1,
    (interleave_values first.bits second.bits).2, Encoding.value_bits, Encoding.value_bits, decide_eq_true_eq]

theorem interleave_length_le (first second : List Bool) :
    (interleave first second).length ≤ 2*(first.length+second.length) := by
  induction first generalizing second with
  | nil =>
      induction second with
      | nil => simp [interleave]
      | cons bit second ih => simp only [interleave, List.length_cons, List.length_nil] at *; omega
  | cons bit first ih =>
      cases second with
      | nil =>
          have bound := ih []
          simp only [interleave, List.length_cons, List.length_nil] at *
          omega
      | cons other second =>
          have bound := ih second
          simp only [interleave, List.length_cons] at *
          omega

/-- General binary comparison on the explicitly stated column layout,
with clean boolean output and a linear number of real transitions. -/
theorem comparison_natural_clean (first second : Nat) :
    ∃ steps output, steps ≤ 4*(first.size+second.size)+1 ∧
      HaltsAt comparisonProgram (interleave first.bits second.bits) steps output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.boolean.encode (decide (first ≤ second))).map bitSymbol) := by
  refine ⟨_, _, ?_, comparison_halts _, ?_⟩
  · have bound := interleave_length_le first.bits second.bits
    simp only [Encoding.bits_length] at bound
    omega
  · rw [← comparison_natural]
    exact comparison_clean _

end Counting.Machine
