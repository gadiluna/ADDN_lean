import Counting.ExternalInitialRowsSize
import Counting.ExternalMachineInitial
import Counting.ComplexityModel

/-! The bounded-computation part of Cook–Levin. The reduction is an actual
Lean function producing CNF, and the iff refers to the fixed machine model's
primitive transitions. ExternalCookLevinMachine implements this generator
as a polynomial-time Turing transducer for the reduction. -/
namespace Counting.External.CookLevin
open Machine InitialRows MachineBridge

def capacity (input : List Bool) (witnessBound : ℕ) : ℕ :=
  (Encoding.frame input).length+witnessBound

def setup (input : List Bool) (witnessBound time : ℕ) :
    Setup (width (capacity input witnessBound) time) where
  offset := ⟨time+1, by unfold width; omega⟩
  header := Encoding.frame input
  capacity := witnessBound
  fits := by
    change time+1+(Encoding.frame input).length+witnessBound ≤ width (capacity input witnessBound) time
    unfold width capacity
    omega

theorem configuration_eq_initial (program : Program) (input witness : List Bool) (witnessBound time : ℕ) :
    ((setup input witnessBound time).configuration program witness) =
      initialConfig program (Encoding.pairWords input witness) (capacity input witnessBound) time := by
  unfold Setup.configuration initialConfig
  congr 1
  funext place
  exact (initial_tape program (Encoding.pairWords input witness) (capacity input witnessBound) time place).symm

def boundedFormula (program : Program) (input : List Bool) (witnessBound time : ℕ) :=
  (setup input witnessBound time).formula program (finRotate (width (capacity input witnessBound) time)) time

def boundedInput (program : Program) (input : List Bool) (witnessBound time : ℕ) : CNFInput :=
  ⟨((time+1)*width (capacity input witnessBound) time)*Cellular.alphabet program,
    boundedFormula program input witnessBound time⟩

/-- No abstract tableau-validity hypothesis remains: satisfiability is
equivalent to a short witness and a genuine bounded halted accepting run. -/
theorem boundedFormula_satisfiable_iff (program : Program) (input : List Bool) (witnessBound time : ℕ) :
    (boundedFormula program input witnessBound time).Satisfiable ↔
      ∃ witness : List Bool, witness.length ≤ witnessBound ∧
        ∃ steps ≤ time, ∃ output,
          HaltsAt program (Encoding.pairWords input witness) steps output ∧ program.accept output.control = true := by
  unfold boundedFormula Setup.formula
  rw [Tableau.satisfiable_iff]
  constructor
  · rintro ⟨config, initialAccepted, finalAccepted⟩
    obtain ⟨witness, bounded, rfl⟩ :=
      ((setup input witnessBound time).constraints_exists_iff program config).mp initialAccepted
    rw [configuration_eq_initial] at finalAccepted
    exact ⟨witness, bounded, (bounded_accepts_iff program _ _ _).mp finalAccepted⟩
  · rintro ⟨witness, bounded, accepted⟩
    refine ⟨((setup input witnessBound time).configuration program witness).encoded,
      ((setup input witnessBound time).constraints_exists_iff program _).mpr ⟨witness, bounded, rfl⟩, ?_⟩
    rw [configuration_eq_initial]
    exact (bounded_accepts_iff program _ _ _).mpr accepted

theorem polynomial_mono (coefficient exponent : ℕ) {first second : ℕ} (ordered : first ≤ second) :
    Complexity.polynomial coefficient exponent first ≤ Complexity.polynomial coefficient exponent second :=
  Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (by omega) exponent)

def timeBound (coefficient exponent : ℕ) (input : List Bool) (witnessBound : ℕ) : ℕ :=
  Complexity.polynomial coefficient exponent (capacity input witnessBound)

/-- A verifier that halts within its stated bound may be represented by a
single tableau time bound shared by all admissible witness lengths. -/
theorem verifierFormula_satisfiable_iff (program : Program) (coefficient exponent : ℕ)
    (running : Complexity.RunsIn program (Complexity.polynomial coefficient exponent))
    (input : List Bool) (witnessBound : ℕ) :
    (boundedFormula program input witnessBound (timeBound coefficient exponent input witnessBound)).Satisfiable ↔
      ∃ witness : List Bool, witness.length ≤ witnessBound ∧ Accepts program (Encoding.pairWords input witness) := by
  rw [boundedFormula_satisfiable_iff]
  constructor
  · rintro ⟨witness, bounded, steps, _, output, halted, accepted⟩
    exact ⟨witness, bounded, steps, output, halted, accepted⟩
  · rintro ⟨witness, bounded, accepted⟩
    obtain ⟨steps, output, cost, halted⟩ := running (Encoding.pairWords input witness)
    have lengthBound : (Encoding.pairWords input witness).length ≤ capacity input witnessBound := by
      simp only [Encoding.pairWords, List.length_append, capacity]
      omega
    refine ⟨witness, bounded, steps, cost.trans (polynomial_mono coefficient exponent lengthBound), output,
      halted, ?_⟩
    exact (Machine.accepts_iff_of_halts halted).mp accepted

def reduceInput (program : Program) (coefficient exponent witnessCoefficient witnessExponent : ℕ)
    (input : List Bool) : CNFInput :=
  let witnessBound := Complexity.polynomial witnessCoefficient witnessExponent input.length
  boundedInput program input witnessBound (timeBound coefficient exponent input witnessBound)

def reduce (program : Program) (coefficient exponent witnessCoefficient witnessExponent : ℕ)
    (input : List Bool) : List Bool :=
  CNFEncoding.codec.encode (reduceInput program coefficient exponent witnessCoefficient witnessExponent input)

def SAT : Complexity.Language := Complexity.encodedLanguage CNFEncoding.codec (fun input => input.2.Satisfiable)

/-- Semantic Cook–Levin reduction for every NP verifier. The only remaining
requirement for `ManyOnePoly` is a verified polynomial-time machine that
computes the already defined function `reduce`. -/
theorem reduce_yes_iff (program : Program) (coefficient exponent witnessCoefficient witnessExponent : ℕ)
    (running : Complexity.RunsIn program (Complexity.polynomial coefficient exponent))
    (language : Complexity.Language)
    (verified : ∀ input, input ∈ language ↔ ∃ witness : List Bool,
      witness.length ≤ Complexity.polynomial witnessCoefficient witnessExponent input.length ∧
        Accepts program (Encoding.pairWords input witness)) (input : List Bool) :
    reduce program coefficient exponent witnessCoefficient witnessExponent input ∈ SAT ↔ input ∈ language := by
  rw [reduce, SAT, Complexity.encodedLanguage_iff]
  exact (verifierFormula_satisfiable_iff program coefficient exponent running input _).trans (verified input).symm

theorem NP_exists_reduction (language : Complexity.Language) (np : Complexity.NP language) :
    ∃ program coefficient exponent witnessCoefficient witnessExponent,
      Complexity.RunsIn program (Complexity.polynomial coefficient exponent) ∧
      ∀ input, reduce program coefficient exponent witnessCoefficient witnessExponent input ∈ SAT ↔ input ∈ language := by
  obtain ⟨program, coefficient, exponent, witnessCoefficient, witnessExponent, running, verified⟩ := np
  exact ⟨program, coefficient, exponent, witnessCoefficient, witnessExponent, running,
    reduce_yes_iff program coefficient exponent witnessCoefficient witnessExponent running language verified⟩

end Counting.External.CookLevin
