import DirectedCountingFormalization.GaussianGeneratorCompleteness

/-! Small kernel-reduced edge cases for the replay-checked rational solver.
These tests supplement, and do not replace, the general soundness/completeness proofs.
-/

namespace DirectedCounting.ComponentTests

open VerifiedGaussianAnchorSolver

private def uniqueSystem : RationalSystem 2 where
  coeff := !![2, 1; 1, -1]
  rhs := ![5, 1]

example : uniqueSystem.solve? = some ![2, 1] := by decide +kernel

private def singularSystem : RationalSystem 2 where
  coeff := !![1, 1; 2, 2]
  rhs := ![2, 4]

example : singularSystem.solve? = none := by decide +kernel

private def inconsistentSystem : RationalSystem 2 where
  coeff := !![1, 1; 2, 2]
  rhs := ![2, 5]

example : inconsistentSystem.solve? = none := by decide +kernel

private def rationalSystem : RationalSystem 1 where
  coeff := !![2]
  rhs := ![1]

example : rationalSystem.solve? = some ![(1 : ℚ) / 2] := by decide +kernel

example : ExactAnchorSolver.rationalVectorToNat? ![(1 : ℚ) / 2] = none := by decide +kernel
example : ExactAnchorSolver.rationalVectorToNat? ![(-1 : ℚ)] = none := by decide +kernel

/-- Invalid replay transcripts cannot certify a zero scaling. -/
example : uniqueSystem.verifyTranscript [.scale 0 0] = none := by decide +kernel

/-- A zero-dimensional system has the unique empty vector. -/
example : RationalSystem.solve? (q := 0) ⟨0, 0⟩ = some 0 := by decide +kernel

end DirectedCounting.ComponentTests
