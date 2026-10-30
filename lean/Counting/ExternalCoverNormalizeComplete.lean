import Counting.ExternalCoverNormalizeMachine

namespace Counting.External.CoverNormalization

theorem normalizedInput_parameters (input : X3CEncoding.Input) :
    2 ≤ (X3CEncoding.normalizedInput input).1 ∧
      Function.Injective (X3CEncoding.normalizedInput input).2.2.triples ∧
      (X3CEncoding.normalizedInput input).2.1 ≤ input.2.1+2 := by
  obtain ⟨orderBound,rowBound⟩ := input.2.2.normalize_parameters
  exact ⟨orderBound,input.2.2.normalize.distinct,rowBound⟩

/-- Every output is a valid normalized instance, including the fallback on
arbitrary malformed source words. The explicit universe has at least six
elements and the listed triples have no duplicates. -/
theorem normalizeWord_parameters (word : List Bool) :
    ∃ input : X3CEncoding.Input,
      X3CEncoding.codec.encode input=normalizeWord word ∧
      2 ≤ input.1 ∧ Function.Injective input.2.2.triples := by
  cases decoded : X3CEncoding.codec.decodeExact word with
  | none=>
    exact ⟨X3CEncoding.normalizedInput CoverMachine.rejectCover,
      by simp [normalizeWord,decoded,rejectedOutput],
      (normalizedInput_parameters CoverMachine.rejectCover).1,
      (normalizedInput_parameters CoverMachine.rejectCover).2.1⟩
  | some input=>
    exact ⟨X3CEncoding.normalizedInput input,by simp [normalizeWord,decoded],
      (normalizedInput_parameters input).1,(normalizedInput_parameters input).2.1⟩

/-- All claims of X3C preprocessing together: a total, clean, polynomial
finite-alphabet Turing transducer, exact-cover equivalence, and normalized
parameters for its actual serialized output. -/
theorem normalization_complete :
    Complexity.ComputesCleanIn machineGenerator normalizeWord
      (Complexity.polynomial (20*(entryCoefficient+67)^2) 12) ∧
    (∀ word,X3CEncoding.BinaryX3C (normalizeWord word) ↔ X3CEncoding.BinaryX3C word) ∧
    (∀ word,∃ input : X3CEncoding.Input,
      X3CEncoding.codec.encode input=normalizeWord word ∧
      2 ≤ input.1 ∧ Function.Injective input.2.2.triples) :=
  ⟨machineGenerator_computesCleanIn,normalizeWord_yes_iff,normalizeWord_parameters⟩

end Counting.External.CoverNormalization
