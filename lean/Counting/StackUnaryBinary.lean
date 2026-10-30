import Counting.StackUnaryLength
import Counting.MachineBinary

namespace Counting.StackMachine.Unary

/-- Consume an arbitrary bit counter and increment a canonical little-endian
accumulator once per bit. Scratch stores the carry prefix only. -/
def toBinaryProgram (extra : Nat) (counter accumulator scratch : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 6
  code state := match state.val with
    | 0 => .pop counter 6 1 1
    | 1 => .pop accumulator 3 3 2
    | 2 => .push scratch false 1
    | 3 => .push accumulator true 4
    | 4 => .pop scratch 0 5 5
    | 5 => .push accumulator false 4
    | _ => .halt

def binaryConfig (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (state : Control (toBinaryProgram extra counter accumulator scratch))
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    Config (toBinaryProgram extra counter accumulator scratch) :=
  ⟨state, fun r => if r=counter then unary else if r=accumulator then binary else if r=scratch then work else base r⟩

theorem restore_bit (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (unary binary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch)) 2
      (binaryConfig extra counter accumulator scratch 4 base unary binary (bit::work)) =
      some (binaryConfig extra counter accumulator scratch 4 base unary (false::binary) work) := by
  have ac := Ne.symm ca
  have sc := Ne.symm cs
  have sa := Ne.symm as
  cases bit <;> dsimp [Machine.run, step, toBinaryProgram, binaryConfig]
  all_goals
    simp_all
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=counter
    · subst r; simp_all
    · by_cases b : r=accumulator
      · subst r; simp_all
      · by_cases c : r=scratch
        · subst r; simp_all
        · simp_all

theorem restore_empty (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (unary binary : List Bool) :
    step (toBinaryProgram extra counter accumulator scratch)
      (binaryConfig extra counter accumulator scratch 4 base unary binary []) =
      some (binaryConfig extra counter accumulator scratch 0 base unary binary []) := by
  have sc := Ne.symm cs
  have sa := Ne.symm as
  dsimp [step, toBinaryProgram, binaryConfig]
  simp_all
  rfl

theorem restore_run (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch)) (2*work.length+1)
      (binaryConfig extra counter accumulator scratch 4 base unary binary work) =
      some (binaryConfig extra counter accumulator scratch 0 base unary (List.replicate work.length false++binary) []) := by
  induction work generalizing binary with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, restore_empty _ _ _ _ cs as, Option.bind_some]
      rfl
  | cons bit work ih =>
      rw [List.length_cons, show 2*(work.length+1)+1=2+(2*work.length+1) by omega,
        Machine.run_add, restore_bit extra counter accumulator scratch ca cs as, Option.bind_some, ih]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem carry_one (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch)) 2
      (binaryConfig extra counter accumulator scratch 1 base unary (true::binary) work) =
      some (binaryConfig extra counter accumulator scratch 1 base unary binary (false::work)) := by
  have sc := Ne.symm cs
  have sa := Ne.symm as
  have ac := Ne.symm ca
  dsimp [Machine.run, step, toBinaryProgram, binaryConfig]
  simp_all
  refine ⟨rfl, ?_⟩
  funext r
  by_cases a : r=counter
  · subst r; simp_all
  · by_cases b : r=accumulator
    · subst r; simp_all
    · by_cases c : r=scratch
      · subst r; simp_all
      · simp_all

theorem carry_zero (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator)
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch)) 2
      (binaryConfig extra counter accumulator scratch 1 base unary (false::binary) work) =
      some (binaryConfig extra counter accumulator scratch 4 base unary (true::binary) work) := by
  have ac := Ne.symm ca
  dsimp [Machine.run, step, toBinaryProgram, binaryConfig]
  simp_all
  refine ⟨rfl, ?_⟩
  funext r
  by_cases a : r=counter
  · subst r; simp_all
  · by_cases b : r=accumulator
    · subst r; simp_all
    · simp_all

theorem carry_empty (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator)
    (base : Fin (extra+3) → List Bool) (unary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch)) 2
      (binaryConfig extra counter accumulator scratch 1 base unary [] work) =
      some (binaryConfig extra counter accumulator scratch 4 base unary [true] work) := by
  have ac := Ne.symm ca
  dsimp [Machine.run, step, toBinaryProgram, binaryConfig]
  simp_all
  refine ⟨rfl, ?_⟩
  funext r
  by_cases a : r=counter
  · subst r; simp_all
  · by_cases b : r=accumulator
    · subst r; simp_all
    · simp_all

theorem increment_run (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    Machine.run (step (toBinaryProgram extra counter accumulator scratch))
      (4*Machine.carryLength binary+2*work.length+3)
      (binaryConfig extra counter accumulator scratch 1 base unary binary work) =
      some (binaryConfig extra counter accumulator scratch 0 base unary
        (List.replicate work.length false++Machine.increment binary) []) := by
  induction binary generalizing work with
  | nil =>
      rw [show 4*Machine.carryLength []+2*work.length+3=2+(2*work.length+1) by simp only [Machine.carryLength]; omega,
        Machine.run_add, carry_empty _ _ _ _ ca, Option.bind_some,
        restore_run _ _ _ _ ca cs as]
      rfl
  | cons bit binary ih =>
      cases bit with
      | false =>
          rw [show 4*Machine.carryLength (false::binary)+2*work.length+3=2+(2*work.length+1) by simp only [Machine.carryLength]; omega,
            Machine.run_add, carry_zero _ _ _ _ ca, Option.bind_some,
            restore_run _ _ _ _ ca cs as]
          rfl
      | true =>
          have time : 4*Machine.carryLength (true::binary)+2*work.length+3 =
              2+(4*Machine.carryLength binary+2*(false::work).length+3) := by
            simp only [Machine.carryLength, List.length_cons]
            omega
          rw [time, Machine.run_add, carry_one _ _ _ _ ca cs as, Option.bind_some, ih]
          simp only [List.length_cons, List.replicate_succ', List.append_assoc,
            List.singleton_append, Machine.increment]

theorem consume_bit (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (bit : Bool) (unary binary work : List Bool) :
    step (toBinaryProgram extra counter accumulator scratch)
      (binaryConfig extra counter accumulator scratch 0 base (bit::unary) binary work) =
      some (binaryConfig extra counter accumulator scratch 1 base unary binary work) := by
  cases bit <;> dsimp [step, toBinaryProgram, binaryConfig] <;> simp
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=counter
    · subst r; simp
    · simp [a]

theorem consume_empty (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (binary work : List Bool) :
    step (toBinaryProgram extra counter accumulator scratch)
      (binaryConfig extra counter accumulator scratch 0 base [] binary work) =
      some (binaryConfig extra counter accumulator scratch 6 base [] binary work) := by
  dsimp [step, toBinaryProgram, binaryConfig]
  simp
  rfl

theorem toBinary_run (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (base : Fin (extra+3) → List Bool) (unary : List Bool) (initial : Nat) :
    ∃ transitions ≤ 4*unary.length*(initial+unary.length+1)+1,
      Machine.run (step (toBinaryProgram extra counter accumulator scratch)) transitions
        (binaryConfig extra counter accumulator scratch 0 base unary initial.bits []) =
        some (binaryConfig extra counter accumulator scratch 6 base [] (initial+unary.length).bits []) := by
  induction unary generalizing initial with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      rw [Machine.run, consume_empty, Option.bind_some]
      rfl
  | cons bit unary ih =>
      obtain ⟨transitions, bounded, executed⟩ := ih (initial+1)
      have carryBound : Machine.carryLength initial.bits ≤ initial :=
        (Machine.carryLength_le initial.bits).trans (by rw [Encoding.bits_length]; exact Nat.size_le.mpr Nat.lt_two_pow_self)
      refine ⟨1+((4*Machine.carryLength initial.bits+3)+transitions), ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · rw [Nat.one_add, Machine.run, consume_bit, Option.bind_some, Machine.run_add]
        have increment := increment_run extra counter accumulator scratch ca cs as base unary initial.bits []
        simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, List.replicate_zero,
          List.nil_append, Machine.increment_bits] at increment
        rw [increment, Option.bind_some, executed]
        have total : initial+1+unary.length=initial+(bit::unary).length := by simp; omega
        rw [total]

theorem toBinary_halted (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (unary binary work : List Bool) :
    step (toBinaryProgram extra counter accumulator scratch)
      (binaryConfig extra counter accumulator scratch 6 base unary binary work) = none := rfl

/-- Any bit list serves as a unary counter; its length, not its bit values,
determines the canonical natural payload produced by the program. -/
theorem toBinary_computes : ComputesIn (toBinaryProgram 0 0 1 2)
    (fun input => input.length.bits) (fun length => 4*length*(length+1)+1) := by
  intro input
  let base : Fin 3 → List Bool := fun _ => []
  obtain ⟨transitions, bounded, executed⟩ :=
    toBinary_run 0 0 1 2 (by decide) (by decide) (by decide) base input 0
  refine ⟨transitions, binaryConfig 0 0 1 2 6 base [] input.length.bits [], ?_,
    ⟨?_, toBinary_halted _ _ _ _ _ _ _ _⟩, rfl⟩
  · simpa only [Nat.zero_add] using bounded
  · have start : StackMachine.initial (toBinaryProgram 0 0 1 2) input =
        binaryConfig 0 0 1 2 0 base input [] [] := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [start]
    simpa only [Nat.zero_add, Nat.zero_bits] using executed

end Counting.StackMachine.Unary
