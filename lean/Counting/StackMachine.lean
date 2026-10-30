import Counting.MachineModel
import Counting.EncodingBinary

/-! An executable fixed-register stack language for verified compilation.
Its abstract transitions are not Turing transitions: a compiler must prove
the physical simulation and its cost before using this language for a
complexity claim. Every register contains a list of bits. -/
namespace Counting.StackMachine
open Machine
open scoped BigOperators

inductive Instruction (registers states : ℕ) where
  | halt
  | jump (next : Fin states)
  | push (register : Fin registers) (bit : Bool) (next : Fin states)
  | pop (register : Fin registers) (empty zero one : Fin states)
deriving DecidableEq, Repr

structure Program where
  extraRegisters : ℕ
  states : ℕ
  code : Fin (states+1) → Instruction (extraRegisters+2) (states+1)

abbrev Register (program : Program) := Fin (program.extraRegisters+2)
abbrev Control (program : Program) := Fin (program.states+1)

structure Config (program : Program) where
  control : Control program
  store : Register program → List Bool

def initial (program : Program) (input : List Bool) : Config program :=
  ⟨0, fun register => if register = 0 then input else []⟩

def step (program : Program) (config : Config program) : Option (Config program) :=
  match program.code config.control with
  | .halt => none
  | .jump next => some {config with control := next}
  | .push register bit next =>
      some ⟨next, Function.update config.store register (bit::config.store register)⟩
  | .pop register empty zero one =>
      match config.store register with
      | [] => some {config with control := empty}
      | bit::rest => some ⟨if bit then one else zero, Function.update config.store register rest⟩

def Config.dataLength {program : Program} (config : Config program) : ℕ :=
  ∑ register, (config.store register).length

def HaltsAt (program : Program) (input : List Bool) (steps : ℕ) (output : Config program) : Prop :=
  Machine.run (step program) steps (initial program input) = some output ∧ step program output = none

def ComputesIn (program : Program) (function : List Bool → List Bool) (bound : ℕ → ℕ) : Prop :=
  ∀ input, ∃ steps output, steps ≤ bound input.length ∧ HaltsAt program input steps output ∧ output.store 1 = function input

theorem initial_dataLength (program : Program) (input : List Bool) :
    (initial program input).dataLength = input.length := by
  simp only [Config.dataLength, initial]
  simp_rw [apply_ite List.length]
  simp

theorem update_length_le {registers : ℕ} (store : Fin registers → List Bool)
    (register : Fin registers) (value : List Bool) (bounded : value.length ≤ (store register).length+1) :
    (∑ i, ((Function.update store register value) i).length) ≤ (∑ i, (store i).length)+1 := by
  calc
    _ ≤ ∑ i, ((store i).length + if i = register then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases same : i = register
      · subst i
        simpa using bounded
      · simp [same]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem step_dataLength {program : Program} (config next : Config program)
    (transition : step program config = some next) : next.dataLength ≤ config.dataLength+1 := by
  unfold step at transition
  cases instruction : program.code config.control with
  | halt => simp [instruction] at transition
  | jump target =>
      simp only [instruction, Option.some.injEq] at transition
      subst next
      exact Nat.le_succ _
  | push register bit target =>
      simp only [instruction, Option.some.injEq] at transition
      subst next
      exact update_length_le _ _ _ (by simp)
  | pop register empty zero one =>
      cases contents : config.store register with
      | nil =>
          simp only [instruction, contents, Option.some.injEq] at transition
          subst next
          exact Nat.le_succ _
      | cons bit rest =>
          simp only [instruction, contents, Option.some.injEq] at transition
          subst next
          exact update_length_le _ _ _ (by simp only [contents, List.length_cons]; omega)

theorem run_dataLength {program : Program} (first last : Config program) (steps : ℕ)
    (executed : Machine.run (step program) steps first = some last) :
    last.dataLength ≤ first.dataLength+steps := by
  induction steps generalizing first with
  | zero =>
      have equal : first = last := Option.some.inj executed
      subst first
      exact le_rfl
  | succ steps ih =>
      cases transition : step program first with
      | none => simp only [Machine.run, transition, Option.bind_none] at executed; contradiction
      | some next =>
          have tail : Machine.run (step program) steps next = some last := by
            simpa only [Machine.run, transition, Option.bind_some] using executed
          have bound := ih next tail
          have increase := step_dataLength first next transition
          omega

def block (bits : List Bool) : List Symbol := bits.map bitSymbol ++ [.separator]

def Config.encoded {program : Program} (config : Config program) : List Symbol :=
  .mark :: (List.finRange (program.extraRegisters+2)).flatMap (fun register => block (config.store register))

theorem block_length (bits : List Bool) : (block bits).length = bits.length+1 := by simp [block]

theorem block_ne_blank (bits : List Bool) : ∀ symbol ∈ block bits, symbol ≠ .blank := by
  intro symbol member
  simp only [block, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨bit, _, rfl⟩ | rfl
  · exact bitSymbol_ne_blank bit
  · decide

theorem block_ne_mark (bits : List Bool) : ∀ symbol ∈ block bits, symbol ≠ .mark := by
  intro symbol member
  simp only [block, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨bit, _, rfl⟩ | rfl
  · cases bit <;> decide
  · decide

theorem encoded_length {program : Program} (config : Config program) :
    config.encoded.length = config.dataLength+program.extraRegisters+3 := by
  simp only [Config.encoded, List.length_cons, List.length_flatMap, block_length,
    List.sum_map_add]
  simp only [← List.ofFn_eq_map, List.sum_ofFn, Config.dataLength, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  change config.dataLength+(program.extraRegisters+2)+1 = config.dataLength+program.extraRegisters+3
  omega

theorem encoded_ne_blank {program : Program} (config : Config program) :
    ∀ symbol ∈ config.encoded, symbol ≠ .blank := by
  intro symbol member
  simp only [Config.encoded, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨register, _, member⟩
  · decide
  · exact block_ne_blank _ symbol member

end Counting.StackMachine
