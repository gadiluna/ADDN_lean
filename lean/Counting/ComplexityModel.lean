import Counting.MachineBinary

/-! Complexity classes in the fixed finite-alphabet, finite-control model.
Every running-time claim counts the actual transitions of `Machine.step`.
Reductions require a concrete machine producing the encoded output; an
efficient-looking Lean function alone does not establish such a reduction.
No completeness theorem for SAT or X3C is assumed here. -/
namespace Counting.Complexity

open Machine

abbrev Word := List Bool
abbrev Language := Set Word

def polynomial (coefficient exponent length : Nat) : Nat := coefficient * (length + 1) ^ exponent

def RunsIn (program : Program) (bound : Nat → Nat) : Prop :=
  ∀ input, ∃ steps output, steps ≤ bound input.length ∧ HaltsAt program input steps output

def DecidesIn (program : Program) (language : Language) (bound : Nat → Nat) : Prop :=
  RunsIn program bound ∧ ∀ input, Accepts program input ↔ input ∈ language

def ComputesIn (program : Program) (function : Word → Word) (bound : Nat → Nat) : Prop :=
  ∀ input, ∃ steps output, steps ≤ bound input.length ∧ HaltsAt program input steps output ∧
    output.tape.denotes.right₀ = Turing.ListBlank.mk ((function input).map bitSymbol)

/-- Composable transducers must leave the *whole* output tape in initial
form. In particular there is no unread work data left of the head. A
primitive satisfying only `ComputesIn` needs a verified cleanup routine
before it can be used as a reduction; cleanup is never free by definition. -/
def ComputesCleanIn (program : Program) (function : Word → Word) (bound : Nat → Nat) : Prop :=
  ∀ input, ∃ steps output, steps ≤ bound input.length ∧ HaltsAt program input steps output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((function input).map bitSymbol)

theorem ComputesCleanIn.toComputesIn {program : Program} {function : Word → Word} {bound : Nat → Nat}
    (clean : ComputesCleanIn program function bound) : ComputesIn program function bound := by
  intro input
  obtain ⟨steps, output, cost, halted, tape⟩ := clean input
  refine ⟨steps, output, cost, halted, ?_⟩
  rw [tape]
  exact Turing.Tape.mk'_right₀ _ _

def P (language : Language) : Prop :=
  ∃ program coefficient exponent, DecidesIn program language (polynomial coefficient exponent)

/-- Polynomial certificates and a deterministic verifier that halts in
polynomial time on every binary input, including malformed encodings. -/
def NP (language : Language) : Prop :=
  ∃ verifier timeCoefficient timeExponent witnessCoefficient witnessExponent,
    RunsIn verifier (polynomial timeCoefficient timeExponent) ∧
    ∀ input, input ∈ language ↔ ∃ witness : Word,
      witness.length ≤ polynomial witnessCoefficient witnessExponent input.length ∧
        Accepts verifier (Encoding.pairWords input witness)

def coNP (language : Language) : Prop := NP languageᶜ

def ManyOnePoly (source target : Language) : Prop :=
  ∃ function program coefficient exponent,
    ComputesCleanIn program function (polynomial coefficient exponent) ∧
      ∀ input, input ∈ source ↔ function input ∈ target

def NPHard (language : Language) : Prop := ∀ source, NP source → ManyOnePoly source language
def NPComplete (language : Language) : Prop := NP language ∧ NPHard language
def coNPHard (language : Language) : Prop := ∀ source, coNP source → ManyOnePoly source language
def coNPComplete (language : Language) : Prop := coNP language ∧ coNPHard language
def PNeNP : Prop := ¬ ∀ language, P language ↔ NP language

/-- Inputs outside the image of the codec are rejected. -/
def encodedLanguage {α : Type} (codec : Encoding.Codec α) (property : α → Prop) : Language :=
  {input | ∃ value, codec.encode value = input ∧ property value}

theorem encodedLanguage_iff {α : Type} (codec : Encoding.Codec α) (property : α → Prop) (value : α) :
    codec.encode value ∈ encodedLanguage codec property ↔ property value := by
  constructor
  · rintro ⟨other, same, positive⟩
    exact codec.injective same ▸ positive
  · exact fun positive => ⟨value, rfl, positive⟩

theorem malformed_not_mem {α : Type} (codec : Encoding.Codec α) (property : α → Prop) (input : Word)
    (malformed : ∀ value, codec.encode value ≠ input) : input ∉ encodedLanguage codec property := by
  rintro ⟨value, same, _⟩
  exact malformed value same

/-- The explicit four-state incrementer meets a linear transition bound. -/
theorem increment_computesIn : ComputesIn incrementProgram increment (polynomial 3 1) := by
  intro input
  refine ⟨3 * carryLength input + 3, _, ?_, increment_halts input, increment_output input⟩
  simpa only [polynomial, pow_one, Nat.mul_add, Nat.mul_one] using increment_steps_le input

end Counting.Complexity
