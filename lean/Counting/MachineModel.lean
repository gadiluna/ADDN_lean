import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! A fixed finite-alphabet, finite-control Post-Turing model. One write or
one unit head movement costs exactly one transition. The list zipper is an
executable tape representation; its simulation of mathlib TM0 preserves
individual transitions and their exact count. -/
namespace Counting.Machine

inductive Symbol where
  | blank | zero | one | separator | mark
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The input alphabet has two symbols, both different from tape blank. -/
def bitSymbol (bit : Bool) : Symbol := if bit then .one else .zero

@[simp] theorem bitSymbol_ne_blank (bit : Bool) : bitSymbol bit ≠ .blank := by cases bit <;> decide

theorem bitSymbol_injective : Function.Injective bitSymbol := by
  intro a b equal
  cases a <;> cases b <;> cases equal <;> rfl

structure Program where
  /-- There are `states+1` control states; state zero is initial. -/
  states : Nat
  code : Turing.TM0.Machine Symbol (Fin (states + 1))
  accept : Fin (states + 1) → Bool

abbrev Control (program : Program) := Fin (program.states + 1)

@[simp] theorem alphabet_card : Fintype.card Symbol = 5 := by decide
@[simp] theorem control_card (program : Program) : Fintype.card (Control program) = program.states + 1 := Fintype.card_fin _

theorem control_supported (program : Program) : Turing.TM0.Supports program.code Set.univ :=
  Turing.TM0.univ_supports program.code

structure Tape where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving DecidableEq, Repr

def Tape.ofWord (word : List Symbol) : Tape := ⟨[], word.headD .blank, word.tail⟩

def Tape.write (tape : Tape) (symbol : Symbol) : Tape := { tape with head := symbol }

def Tape.move (tape : Tape) : Turing.Dir → Tape
  | .left => ⟨tape.left.tail, tape.left.headD .blank, tape.head :: tape.right⟩
  | .right => ⟨tape.head :: tape.left, tape.right.headD .blank, tape.right.tail⟩

def Tape.denotes (tape : Tape) : Turing.Tape Symbol :=
  ⟨tape.head, Turing.ListBlank.mk tape.left, Turing.ListBlank.mk tape.right⟩

@[simp] theorem Tape.denotes_write (tape : Tape) (symbol : Symbol) :
    (tape.write symbol).denotes = tape.denotes.write symbol := rfl

@[simp] theorem Tape.denotes_move (tape : Tape) (direction : Turing.Dir) :
    (tape.move direction).denotes = tape.denotes.move direction := by
  cases direction <;> cases tape with
  | mk left head right =>
      cases left <;> cases right <;> rfl

@[simp] theorem Tape.denotes_ofWord (word : List Symbol) :
    (Tape.ofWord word).denotes = Turing.Tape.mk₁ word := by
  cases word <;> rfl

structure Config (program : Program) where
  control : Control program
  tape : Tape

def Config.denotes {program : Program} (config : Config program) :
    Turing.TM0.Cfg Symbol (Control program) := ⟨config.control, config.tape.denotes⟩

def initial (program : Program) (input : List Bool) : Config program :=
  ⟨0, Tape.ofWord (input.map bitSymbol)⟩

def step (program : Program) (config : Config program) : Option (Config program) :=
  (program.code config.control config.tape.head).map (fun (control, action) =>
    ⟨control, match action with
      | .move direction => config.tape.move direction
      | .write symbol => config.tape.write symbol⟩)

/-- The executable zipper performs exactly one mathlib TM0 transition. -/
theorem step_simulates (program : Program) (config : Config program) :
    (step program config).map Config.denotes = Turing.TM0.step program.code config.denotes := by
  simp only [step, Turing.TM0.step, Config.denotes, Tape.denotes]
  cases hnext : program.code config.control config.tape.head with
  | none => rfl
  | some result =>
      rcases result with ⟨q, action⟩
      cases action with
      | move direction =>
          change some (⟨q, (config.tape.move direction).denotes⟩ : Turing.TM0.Cfg Symbol (Control program)) =
            some ⟨q, config.tape.denotes.move direction⟩
          rw [Tape.denotes_move]
      | write symbol => rfl

/-- Exactly `steps` successful transitions. A halted machine cannot be
padded with extra transitions. -/
def run {Config : Type*} (transition : Config → Option Config) : Nat → Config → Option Config
  | 0, config => some config
  | steps + 1, config => (transition config).bind (run transition steps)

@[simp] theorem run_zero {Config : Type*} (transition : Config → Option Config) (config : Config) :
    run transition 0 config = some config := rfl

theorem run_add {Config : Type*} (transition : Config → Option Config) (a b : Nat) (config : Config) :
    run transition (a + b) config = (run transition a config).bind (run transition b) := by
  induction a generalizing config with
  | zero => simp only [Nat.zero_add, run, Option.bind_some]
  | succ a ih =>
      simp only [Nat.succ_add, run, ih, Option.bind_assoc]

theorem run_simulation {A B : Type*} (left : A → Option A) (right : B → Option B) (decode : A → B)
    (simulation : ∀ a, (left a).map decode = right (decode a)) (steps : Nat) (config : A) :
    (run left steps config).map decode = run right steps (decode config) := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      simp only [run]
      rw [← simulation config]
      cases hnext : left config with
      | none => rfl
      | some next => simpa only [Option.map_some, Option.bind_some] using ih next

/-- This is a step-count-preserving simulation, not an unbounded
computability reduction. -/
theorem run_simulates (program : Program) (steps : Nat) (config : Config program) :
    (run (step program) steps config).map Config.denotes =
      run (Turing.TM0.step program.code) steps config.denotes :=
  run_simulation _ _ _ (step_simulates program) steps config

theorem run_reaches {Config : Type*} (transition : Config → Option Config) (steps : Nat)
    (first last : Config) (success : run transition steps first = some last) :
    StateTransition.Reaches transition first last := by
  induction steps generalizing first with
  | zero => exact Option.some.inj success ▸ Relation.ReflTransGen.refl
  | succ steps ih =>
      cases hnext : transition first with
      | none => simp only [run, hnext, Option.bind_none] at success; contradiction
      | some next =>
          have tail : run transition steps next = some last := by
            simpa only [run, hnext, Option.bind_some] using success
          exact Relation.ReflTransGen.head hnext (ih next tail)

/-- Acceptance and transduction always require an actual halted execution. -/
def HaltsAt (program : Program) (input : List Bool) (steps : Nat) (output : Config program) : Prop :=
  run (step program) steps (initial program input) = some output ∧ step program output = none

def Accepts (program : Program) (input : List Bool) : Prop :=
  ∃ steps output, HaltsAt program input steps output ∧ program.accept output.control = true

theorem terminal_unique {Config : Type*} (transition : Config → Option Config)
    (first final₁ final₂ : Config) (steps₁ steps₂ : Nat)
    (run₁ : run transition steps₁ first = some final₁) (halt₁ : transition final₁ = none)
    (run₂ : run transition steps₂ first = some final₂) (halt₂ : transition final₂ = none) :
    final₁ = final₂ := by
  induction steps₁ generalizing first steps₂ with
  | zero =>
      have equal : first = final₁ := Option.some.inj run₁
      subst first
      cases steps₂ with
      | zero => exact Option.some.inj run₂
      | succ steps₂ => simp only [run, halt₁, Option.bind_none] at run₂; contradiction
  | succ steps₁ ih =>
      cases hnext : transition first with
      | none => simp only [run, hnext, Option.bind_none] at run₁; contradiction
      | some next =>
          have tail₁ : run transition steps₁ next = some final₁ := by
            simpa only [run, hnext, Option.bind_some] using run₁
          cases steps₂ with
          | zero =>
              have equal : first = final₂ := Option.some.inj run₂
              rw [equal, halt₂] at hnext
              contradiction
          | succ steps₂ =>
              have tail₂ : run transition steps₂ next = some final₂ := by
                simpa only [run, hnext, Option.bind_some] using run₂
              exact ih next steps₂ tail₁ tail₂

theorem HaltsAt.unique {program : Program} {input : List Bool} {steps₁ steps₂ : Nat}
    {final₁ final₂ : Config program} (first : HaltsAt program input steps₁ final₁)
    (second : HaltsAt program input steps₂ final₂) : final₁ = final₂ :=
  terminal_unique _ _ _ _ _ _ first.1 first.2 second.1 second.2

theorem accepts_iff_of_halts {program : Program} {input : List Bool} {steps : Nat}
    {output : Config program} (halted : HaltsAt program input steps output) :
    Accepts program input ↔ program.accept output.control = true := by
  constructor
  · rintro ⟨otherSteps, otherOutput, otherHalts, accepted⟩
    exact otherHalts.unique halted ▸ accepted
  · exact fun accepted => ⟨steps, output, halted, accepted⟩

theorem haltsAt_tm0 {program : Program} {input : List Bool} {steps : Nat} {output : Config program}
    (halted : HaltsAt program input steps output) :
    run (Turing.TM0.step program.code) steps (Turing.TM0.init (input.map bitSymbol)) = some output.denotes ∧
      Turing.TM0.step program.code output.denotes = none := by
  constructor
  · have same := run_simulates program steps (initial program input)
    rw [halted.1] at same
    simpa only [initial, Config.denotes, Tape.denotes_ofWord, Option.map_some, Turing.TM0.init, Fin.default_eq_zero] using same.symm
  · rw [← step_simulates program output, halted.2]
    rfl

end Counting.Machine
