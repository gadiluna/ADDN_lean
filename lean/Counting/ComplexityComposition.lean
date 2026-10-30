import Counting.MachineComposition
import Counting.ComplexityComplements

/-! Polynomial closure by the concrete concatenated finite machine. The
size of the intermediate word is derived from the actual tape execution,
not assumed as an additional hypothesis on a reduction. -/
namespace Counting.Complexity
open Machine

def compositionCoefficient (c d j : Nat) : Nat := c + 2 + d * (c + 2) ^ j
def compositionExponent (k j : Nat) : Nat := (k + 1) * (j + 1)

theorem polynomial_composition_bound (n m c k d j : Nat)
    (length : m ≤ n + polynomial c k n + 1) :
    polynomial c k n + 1 + polynomial d j m ≤
      polynomial (compositionCoefficient c d j) (compositionExponent k j) n := by
  have basePositive : 0 < n + 1 := by omega
  have base : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_pow (by omega)
  have power : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right basePositive (by omega)
  have one : 1 ≤ (n + 1) ^ (k + 1) := Nat.one_le_pow _ _ basePositive
  have middle : m + 1 ≤ (c + 2) * (n + 1) ^ (k + 1) := by
    unfold polynomial at length
    nlinarith [Nat.mul_le_mul_left c power]
  have exponent₁ : k + 1 ≤ compositionExponent k j := by unfold compositionExponent; nlinarith
  have exponent₂ : (k + 1) * j ≤ compositionExponent k j := by unfold compositionExponent; nlinarith
  have firstPower := Nat.pow_le_pow_right basePositive exponent₁
  have secondPower := Nat.pow_le_pow_right basePositive exponent₂
  have firstBound : polynomial c k n + 1 ≤ (c + 2) * (n + 1) ^ compositionExponent k j := by
    unfold polynomial
    nlinarith [Nat.mul_le_mul_left c (power.trans firstPower)]
  have secondBound : polynomial d j m ≤ d * (c + 2) ^ j * (n + 1) ^ compositionExponent k j := by
    unfold polynomial
    calc
      d * (m + 1) ^ j ≤ d * ((c + 2) * (n + 1) ^ (k + 1)) ^ j :=
        Nat.mul_le_mul_left d (Nat.pow_le_pow_left middle j)
      _ = d * (c + 2) ^ j * (n + 1) ^ ((k + 1) * j) := by rw [Nat.mul_pow, ← Nat.pow_mul]; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ secondPower
  unfold polynomial compositionCoefficient
  unfold polynomial at firstBound secondBound
  nlinarith

theorem ComputesCleanIn.compose {first second : Program} {f g : Word → Word} {c k d j : Nat}
    (firstComputes : ComputesCleanIn first f (polynomial c k))
    (secondComputes : ComputesCleanIn second g (polynomial d j)) :
    ComputesCleanIn (Machine.compose first second) (g ∘ f)
      (polynomial (compositionCoefficient c d j) (compositionExponent k j)) := by
  intro input
  obtain ⟨firstSteps, firstOutput, firstCost, firstHalts, firstTape⟩ := firstComputes input
  obtain ⟨secondSteps, secondOutput, secondCost, secondHalts, secondTape⟩ := secondComputes (f input)
  obtain ⟨output, halted, tape⟩ := Machine.compose_halts firstHalts firstTape secondHalts
  refine ⟨firstSteps + 1 + secondSteps, output, ?_, halted, tape.trans secondTape⟩
  have bound := polynomial_composition_bound input.length (f input).length c k d j
    (firstComputes.output_length input)
  omega

theorem ManyOnePoly.trans {first middle last : Language}
    (left : ManyOnePoly first middle) (right : ManyOnePoly middle last) : ManyOnePoly first last := by
  obtain ⟨f, firstProgram, c, k, firstComputes, firstCorrect⟩ := left
  obtain ⟨g, secondProgram, d, j, secondComputes, secondCorrect⟩ := right
  exact ⟨g ∘ f, Machine.compose firstProgram secondProgram, compositionCoefficient c d j,
    compositionExponent k j, firstComputes.compose secondComputes,
    fun input => (firstCorrect input).trans (secondCorrect (f input))⟩

theorem ComputesCleanIn.decides {first second : Program} {f : Word → Word} {language : Language}
    {c k d j : Nat} (computes : ComputesCleanIn first f (polynomial c k))
    (decides : DecidesIn second language (polynomial d j)) :
    DecidesIn (Machine.compose first second) {input | f input ∈ language}
      (polynomial (compositionCoefficient c d j) (compositionExponent k j)) := by
  have execution (input : Word) : ∃ steps output,
      steps ≤ polynomial (compositionCoefficient c d j) (compositionExponent k j) input.length ∧
      HaltsAt (Machine.compose first second) input steps output ∧
      ((Machine.compose first second).accept output.control = true ↔ f input ∈ language) := by
    obtain ⟨a, firstOutput, cost₁, halted₁, tape₁⟩ := computes input
    obtain ⟨b, secondOutput, cost₂, halted₂⟩ := decides.1 (f input)
    obtain ⟨output, halted, _, acceptance⟩ := compose_halts_with_accept halted₁ tape₁ halted₂
    refine ⟨a + 1 + b, output, ?_, halted, ?_⟩
    · have bound := polynomial_composition_bound input.length (f input).length c k d j
        (computes.output_length input)
      omega
    · rw [acceptance, ← accepts_iff_of_halts halted₂]
      exact decides.2 (f input)
  constructor
  · intro input
    obtain ⟨steps, output, cost, halted, _⟩ := execution input
    exact ⟨steps, output, cost, halted⟩
  · intro input
    obtain ⟨_, _, _, halted, correct⟩ := execution input
    rw [accepts_iff_of_halts halted]
    exact correct

theorem P.of_reduction {source target : Language} (reduction : ManyOnePoly source target)
    (decidableTarget : P target) : P source := by
  obtain ⟨f, firstProgram, c, k, computes, correct⟩ := reduction
  obtain ⟨secondProgram, d, j, decides⟩ := decidableTarget
  have pullback := computes.decides decides
  have same : {input | f input ∈ target} = source := by
    ext input
    exact (correct input).symm
  rw [same] at pullback
  exact ⟨Machine.compose firstProgram secondProgram, compositionCoefficient c d j,
    compositionExponent k j, pullback⟩

def identityProgram : Program where
  states := 0
  code _ _ := none
  accept _ := true

theorem identity_computes : ComputesCleanIn identityProgram id (polynomial 1 0) := by
  intro input
  refine ⟨0, initial identityProgram input, by simp [polynomial], ⟨rfl, rfl⟩, ?_⟩
  exact Tape.denotes_ofWord _

theorem ManyOnePoly.refl (language : Language) : ManyOnePoly language language :=
  ⟨id, identityProgram, 1, 0, identity_computes, fun _ => Iff.rfl⟩

theorem NPHard.of_reduction {source target : Language} (hard : NPHard source)
    (reduction : ManyOnePoly source target) : NPHard target :=
  fun language member => (hard language member).trans reduction

theorem coNPHard.of_reduction {source target : Language} (hard : coNPHard source)
    (reduction : ManyOnePoly source target) : coNPHard target :=
  fun language member => (hard language member).trans reduction

end Counting.Complexity
