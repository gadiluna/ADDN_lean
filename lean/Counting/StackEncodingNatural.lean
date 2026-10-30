import Counting.StackEncodingCanonical

/-! An actual finite-control recognizer for the exact natural codec. It
rejects missing terminators, extra suffixes, and redundant highest zeros. -/
namespace Counting.StackMachine.EncodingPrograms

def naturalCheck : Bool → List Bool → Bool
  | last, false::rest => last && rest.isEmpty
  | _, true::bit::rest => naturalCheck bit rest
  | _, _ => false

theorem naturalCheck_frame (last : Bool) (payload suffix : List Bool) :
    naturalCheck last (Encoding.frame payload++suffix) =
      (lastPayloadBit last payload && suffix.isEmpty) := by
  induction payload generalizing last with
  | nil => rfl
  | cons bit payload ih => exact ih bit

theorem naturalCheck_malformed (last : Bool) (input : List Bool)
    (invalid : Encoding.unframe input = none) : naturalCheck last input = false := by
  induction input using Encoding.unframe.induct generalizing last with
  | case1 rest => simp [Encoding.unframe] at invalid
  | case2 bit input ih =>
    cases parsed : Encoding.unframe input with
    | none => exact ih bit parsed
    | some value => simp [Encoding.unframe, parsed] at invalid
  | case3 input nofalse notwo =>
    cases input with
    | nil => rfl
    | cons bit rest =>
      cases bit with
      | false => exact (nofalse rest rfl).elim
      | true =>
        cases rest with
        | nil => rfl
        | cons bit rest => exact (notwo bit rest rfl).elim

theorem naturalCheck_encode (value : Nat) :
    naturalCheck true (Encoding.natural.encode value) = true := by
  change naturalCheck true (Encoding.frame value.bits) = true
  have check := naturalCheck_frame true value.bits []
  simp only [List.append_nil, List.isEmpty_nil, Bool.and_true] at check
  rw [check]
  apply (canonicalPayload_iff value.bits).2
  rw [Encoding.value_bits]

theorem naturalCheck_iff (input : List Bool) :
    naturalCheck true input = true ↔ ∃ value, Encoding.natural.encode value = input := by
  constructor
  · intro accepted
    cases parsed : Encoding.unframe input with
    | none => rw [naturalCheck_malformed true input parsed] at accepted; contradiction
    | some pair =>
      obtain ⟨payload, suffix⟩ := pair
      have split := Machine.unframe_sound input payload suffix parsed
      rw [split, naturalCheck_frame, Bool.and_eq_true] at accepted
      have empty : suffix=[] := List.isEmpty_iff.mp accepted.2
      have canonical := (canonicalPayload_iff payload).1 accepted.1
      refine ⟨Encoding.value payload, ?_⟩
      change Encoding.frame (Encoding.value payload).bits = input
      rw [← canonical, split, empty, List.append_nil]
  · rintro ⟨value, rfl⟩
    exact naturalCheck_encode value

theorem naturalCheck_decodeExact (input : List Bool) :
    naturalCheck true input = (Encoding.natural.decodeExact input).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [naturalCheck_iff, Option.isSome_iff_exists]
  exact exists_congr fun value => (Encoding.natural.decodeExact_iff input value).symm

def naturalProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 6
  code control := match control.val with
    | 0 => .pop source 5 2 3
    | 1 => .pop source 5 5 3
    | 2 => .pop source 4 5 5
    | 3 => .pop source 5 1 0
    | 4 => .push target true 6
    | 5 => .push target false 6
    | _ => .halt

def naturalControl (extra : Nat) (source target : Fin (extra+2)) (last : Bool) :
    Control (naturalProgram extra source target) := if last then 0 else 1

def naturalConfig (extra : Nat) (source target : Fin (extra+2))
    (control : Control (naturalProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Config (naturalProgram extra source target) :=
  ⟨control, fun r => if r=source then input else if r=target then output else base r⟩

theorem natural_bit (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) (last bit : Bool) :
    Machine.run (step (naturalProgram extra source target)) 2
      (naturalConfig extra source target (naturalControl extra source target last)
        base (true::bit::input) output) =
      some (naturalConfig extra source target (naturalControl extra source target bit) base input output) := by
  cases last <;> cases bit <;>
    dsimp [Machine.run, step, naturalProgram, naturalControl, naturalConfig] <;> simp
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases same : r=source <;> simp [same]

theorem natural_emit (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (input output : List Bool) (result : Bool) :
    Machine.run (step (naturalProgram extra source target)) 1
      (naturalConfig extra source target (if result then 4 else 5) base input output) =
      some (naturalConfig extra source target 6 base input (result::output)) := by
  cases result <;>
    dsimp [Machine.run, step, naturalProgram, naturalConfig] <;> simp [Ne.symm distinct]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=source
    · subst r; simp [distinct]
    · by_cases second : r=target <;> simp [first, second, Ne.symm distinct]

theorem natural_empty (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (output : List Bool) (last : Bool) :
    Machine.run (step (naturalProgram extra source target)) 2
      (naturalConfig extra source target (naturalControl extra source target last) base [] output) =
      some (naturalConfig extra source target 6 base [] (false::output)) := by
  have first : Machine.run (step (naturalProgram extra source target)) 1
      (naturalConfig extra source target (naturalControl extra source target last) base [] output) =
      some (naturalConfig extra source target 5 base [] output) := by
    cases last <;> simp [Machine.run, step, naturalProgram, naturalControl, naturalConfig] <;> rfl
  rw [show 2=1+1 from rfl, Machine.run_add, first, Option.bind_some]
  exact natural_emit extra source target distinct base [] output false

theorem natural_flag (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (output : List Bool) (last : Bool) :
    Machine.run (step (naturalProgram extra source target)) 3
      (naturalConfig extra source target (naturalControl extra source target last) base [true] output) =
      some (naturalConfig extra source target 6 base [] (false::output)) := by
  have first : Machine.run (step (naturalProgram extra source target)) 2
      (naturalConfig extra source target (naturalControl extra source target last) base [true] output) =
      some (naturalConfig extra source target 5 base [] output) := by
    cases last <;>
      dsimp [Machine.run, step, naturalProgram, naturalControl, naturalConfig] <;> simp
    all_goals
      refine ⟨rfl, ?_⟩
      funext r
      by_cases same : r=source <;> simp [same]
  rw [show 3=2+1 from rfl, Machine.run_add, first, Option.bind_some]
  exact natural_emit extra source target distinct base [] output false

theorem natural_terminator (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (rest output : List Bool) (last : Bool) :
    ∃ time ≤ 3, ∃ suffix,
      Machine.run (step (naturalProgram extra source target)) time
        (naturalConfig extra source target (naturalControl extra source target last) base (false::rest) output) =
        some (naturalConfig extra source target 6 base suffix ((last && rest.isEmpty)::output)) := by
  cases last with
  | false =>
    refine ⟨2, by decide, rest, ?_⟩
    have first : Machine.run (step (naturalProgram extra source target)) 1
        (naturalConfig extra source target (naturalControl extra source target false) base (false::rest) output) =
        some (naturalConfig extra source target 5 base rest output) := by
      dsimp [Machine.run, step, naturalProgram, naturalControl, naturalConfig]
      simp
      refine ⟨rfl, ?_⟩
      funext r
      by_cases same : r=source <;> simp [same]
    rw [show 2=1+1 from rfl, Machine.run_add, first, Option.bind_some]
    exact natural_emit extra source target distinct base rest output false
  | true =>
    have first : Machine.run (step (naturalProgram extra source target)) 2
        (naturalConfig extra source target (naturalControl extra source target true) base (false::rest) output) =
        some (naturalConfig extra source target (if rest.isEmpty then 4 else 5) base rest.tail output) := by
      cases rest with
      | nil =>
        dsimp [Machine.run, step, naturalProgram, naturalControl, naturalConfig]
        simp
        refine ⟨rfl, ?_⟩
        funext r
        by_cases same : r=source <;> simp [same]
      | cons bit rest =>
        cases bit <;>
          dsimp [Machine.run, step, naturalProgram, naturalControl, naturalConfig] <;> simp
        all_goals
          refine ⟨rfl, ?_⟩
          funext r
          by_cases same : r=source <;> simp [same]
    refine ⟨3, le_rfl, rest.tail, ?_⟩
    rw [show 3=2+1 from rfl, Machine.run_add, first, Option.bind_some]
    exact natural_emit extra source target distinct base rest.tail output rest.isEmpty

theorem natural_run (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (input output : List Bool) (last : Bool) :
    ∃ time ≤ input.length+2, ∃ suffix,
      Machine.run (step (naturalProgram extra source target)) time
        (naturalConfig extra source target (naturalControl extra source target last) base input output) =
        some (naturalConfig extra source target 6 base suffix (naturalCheck last input::output)) := by
  induction input using Encoding.unframe.induct generalizing last with
  | case1 rest =>
    obtain ⟨time, bounded, suffix, executed⟩ := natural_terminator extra source target distinct base rest output last
    exact ⟨time, by simp only [List.length_cons]; omega, suffix, executed⟩
  | case2 bit input ih =>
    obtain ⟨time, bounded, suffix, executed⟩ := ih bit
    refine ⟨2+time, by simp only [List.length_cons]; omega, suffix, ?_⟩
    rw [Machine.run_add, natural_bit, Option.bind_some]
    exact executed
  | case3 input nofalse notwo =>
    cases input with
    | nil => exact ⟨2, le_rfl, [], natural_empty extra source target distinct base output last⟩
    | cons bit rest =>
      cases bit with
      | false => exact (nofalse rest rfl).elim
      | true =>
        cases rest with
        | nil => exact ⟨3, le_rfl, [], natural_flag extra source target distinct base output last⟩
        | cons bit rest => exact (notwo bit rest rfl).elim

theorem natural_halted (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (naturalProgram extra source target) (naturalConfig extra source target 6 base input output) = none := rfl

theorem natural_computes : ComputesIn (naturalProgram 0 0 1)
    (fun input => [(Encoding.natural.decodeExact input).isSome]) (fun length => length+2) := by
  intro input
  obtain ⟨time, bounded, suffix, executed⟩ := natural_run 0 0 1 (by decide) (fun _ => []) input [] true
  refine ⟨time, naturalConfig 0 0 1 6 (fun _ => []) suffix [naturalCheck true input], bounded,
    ⟨?_, natural_halted _ _ _ _ _ _⟩, ?_⟩
  · have start : initial (naturalProgram 0 0 1) input =
        naturalConfig 0 0 1 (naturalControl 0 0 1 true) (fun _ => []) input [] := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [start]
    exact executed
  · change [naturalCheck true input] = _
    rw [naturalCheck_decodeExact]

theorem natural_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile (naturalProgram 0 0 1))
      (fun input => [(Encoding.natural.decodeExact input).isSome])
      (Complexity.polynomial (20*(3+0+5)^2) 4) := by
  apply Compiler.computesCleanIn_polynomial 3 1
  intro input
  obtain ⟨time, output, bound, halted, value⟩ := natural_computes input
  refine ⟨time, output, ?_, halted, value⟩
  simp only [Complexity.polynomial, pow_one]
  dsimp only at bound
  omega

end Counting.StackMachine.EncodingPrograms
