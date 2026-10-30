import Counting.MachineBooleanDecision

namespace Counting.Complexity

/-- A clean Boolean transducer yields an NP verifier when its acceptance on
the actual framed input/witness pair is exactly a bounded certificate
relation. Its running-time premise is total, including malformed words. -/
theorem ComputesCleanIn.np_of_bounded_witnesses
    {program : Machine.Program} {predicate : Word → Bool} {language : Language}
    {c k witnessCoefficient witnessExponent : Nat}
    (computes : ComputesCleanIn program (fun input => [predicate input]) (polynomial c k))
    (witnesses : ∀ input, input ∈ language ↔ ∃ witness : Word,
      witness.length ≤ polynomial witnessCoefficient witnessExponent input.length ∧
      predicate (Encoding.pairWords input witness)=true) : NP language := by
  have decision := computes.boolean_decides
  refine ⟨Machine.compose program Machine.booleanDecision,
    compositionCoefficient c 1 0,compositionExponent k 0,
    witnessCoefficient,witnessExponent,decision.1,?_⟩
  intro input
  rw [witnesses input]
  exact exists_congr fun witness => and_congr_right fun _ => (decision.2 _).symm

/-- The same construction proves coNP membership from certificates for
nonmembership, with no decidability or validity assumption on the input. -/
theorem ComputesCleanIn.conp_of_bounded_counterexamples
    {program : Machine.Program} {predicate : Word → Bool} {language : Language}
    {c k witnessCoefficient witnessExponent : Nat}
    (computes : ComputesCleanIn program (fun input => [predicate input]) (polynomial c k))
    (witnesses : ∀ input, input ∉ language ↔ ∃ witness : Word,
      witness.length ≤ polynomial witnessCoefficient witnessExponent input.length ∧
      predicate (Encoding.pairWords input witness)=true) : coNP language :=
  computes.np_of_bounded_witnesses witnesses

end Counting.Complexity
