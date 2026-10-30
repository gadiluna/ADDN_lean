import Counting.StackEncodingUnframeTotal

/-! Finite-control recognition of canonical little-endian payloads. The
empty payload represents zero; every nonempty accepted payload ends in one.
The program reads each bit once and emits a single Boolean answer. -/
namespace Counting.StackMachine.EncodingPrograms

def lastPayloadBit : Bool → List Bool → Bool
  | last, [] => last
  | _, bit::bits => lastPayloadBit bit bits

def canonicalPayload (bits : List Bool) : Bool := lastPayloadBit true bits

theorem lastPayloadBit_append (last : Bool) (first second : List Bool) :
    lastPayloadBit last (first++second) = lastPayloadBit (lastPayloadBit last first) second := by
  induction first generalizing last with
  | nil => rfl
  | cons bit first ih => exact ih bit

theorem canonicalPayload_append (bits : List Bool) (bit : Bool) :
    canonicalPayload (bits++[bit]) = bit := by
  rw [canonicalPayload, lastPayloadBit_append]
  rfl

theorem normalize_length_le (bits : List Bool) :
    (Arithmetic.normalize bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [Arithmetic.normalize]
    split_ifs
    · simp
    · simp only [List.length_cons]
      omega

/-- Exact agreement with the natural-number payload convention, including
rejection of any nonempty representation of zero. -/
theorem canonicalPayload_iff (bits : List Bool) :
    canonicalPayload bits = true ↔ bits = (Encoding.value bits).bits := by
  rw [← Arithmetic.normalize_eq_bits]
  induction bits using List.reverseRecOn with
  | nil => simp [canonicalPayload, lastPayloadBit, Arithmetic.normalize]
  | append_singleton bits bit ih =>
    cases bit with
    | false =>
      rw [canonicalPayload_append, Arithmetic.normalize_append_false]
      have shorter := normalize_length_le bits
      have distinct : bits++[false] ≠ Arithmetic.normalize bits := by
        intro equal
        have lengths := congrArg List.length equal
        simp only [List.length_append, List.length_singleton] at lengths
        omega
      simp [distinct]
    | true => simp only [canonicalPayload_append, Arithmetic.normalize_append_true]

def canonicalProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 4
  code control := match control.val with
    | 0 => .pop source 2 1 0
    | 1 => .pop source 3 1 0
    | 2 => .push target true 4
    | 3 => .push target false 4
    | _ => .halt

def canonicalControl (extra : Nat) (source target : Fin (extra+2)) (last : Bool) :
    Control (canonicalProgram extra source target) := if last then 0 else 1

def canonicalConfig (extra : Nat) (source target : Fin (extra+2))
    (control : Control (canonicalProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Config (canonicalProgram extra source target) :=
  ⟨control, fun r => if r=source then input else if r=target then output else base r⟩

theorem canonical_bit (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) (last bit : Bool) :
    Machine.run (step (canonicalProgram extra source target)) 1
      (canonicalConfig extra source target (canonicalControl extra source target last)
        base (bit::input) output) =
      some (canonicalConfig extra source target (canonicalControl extra source target bit)
        base input output) := by
  cases last <;> cases bit <;>
    dsimp [Machine.run, step, canonicalProgram, canonicalControl, canonicalConfig] <;> simp
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases same : r=source <;> simp [same]

theorem canonical_empty (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (output : List Bool) (last : Bool) :
    Machine.run (step (canonicalProgram extra source target)) 2
      (canonicalConfig extra source target (canonicalControl extra source target last) base [] output) =
      some (canonicalConfig extra source target 4 base [] (last::output)) := by
  cases last <;>
    dsimp [Machine.run, step, canonicalProgram, canonicalControl, canonicalConfig] <;>
    simp [Ne.symm distinct]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=source
    · subst r; simp [distinct]
    · by_cases second : r=target <;> simp [first, second, Ne.symm distinct]

theorem canonical_run (extra : Nat) (source target : Fin (extra+2))
    (distinct : source ≠ target) (base : Fin (extra+2) → List Bool)
    (input output : List Bool) (last : Bool) :
    Machine.run (step (canonicalProgram extra source target)) (input.length+2)
      (canonicalConfig extra source target (canonicalControl extra source target last) base input output) =
      some (canonicalConfig extra source target 4 base [] (lastPayloadBit last input::output)) := by
  induction input generalizing last with
  | nil => exact canonical_empty extra source target distinct base output last
  | cons bit input ih =>
    have time : (bit::input).length+2 = 1+(input.length+2) := by simp; omega
    rw [time, Machine.run_add, canonical_bit, Option.bind_some]
    exact ih bit

theorem canonical_halted (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (canonicalProgram extra source target) (canonicalConfig extra source target 4 base input output) = none := rfl

theorem canonical_computes : ComputesIn (canonicalProgram 0 0 1)
    (fun input => [canonicalPayload input]) (fun length => length+2) := by
  intro input
  refine ⟨input.length+2, canonicalConfig 0 0 1 4 (fun _ => []) [] [canonicalPayload input], le_rfl,
    ⟨?_, canonical_halted _ _ _ _ _ _⟩, rfl⟩
  have start : initial (canonicalProgram 0 0 1) input =
      canonicalConfig 0 0 1 (canonicalControl 0 0 1 true) (fun _ => []) input [] := by
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> rfl
  rw [start]
  exact canonical_run 0 0 1 (by decide) (fun _ => []) input [] true

theorem canonical_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile (canonicalProgram 0 0 1))
      (fun input => [canonicalPayload input]) (Complexity.polynomial (20*(3+0+5)^2) 4) := by
  apply Compiler.computesCleanIn_polynomial 3 1
  intro input
  obtain ⟨time, output, bound, halted, value⟩ := canonical_computes input
  refine ⟨time, output, ?_, halted, value⟩
  simp only [Complexity.polynomial, pow_one]
  dsimp only at bound
  omega

end Counting.StackMachine.EncodingPrograms
