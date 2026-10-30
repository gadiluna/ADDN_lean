import Counting.GaussianIntermediateBounds

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem
open DirectedCounting.GaussianGeneratorCompleteness
open scoped BigOperators Matrix
variable {q : Nat}

structure RunInvariant (original : Augmented q ℤ) (M frontier : Nat) (state : GaussianState q) : Prop where
  safe : SafeState (integralSystem original) (intermediateBound q M) state
  active_basis : state.ok = true → ∃ permutation,
    BasisInvariant original permutation frontier state.system

theorem runInvariant_initial (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) :
    RunInvariant original M 0 ⟨integralSystem original, [], true⟩ :=
  ⟨SafeState.initial _ _ ((basis_initial original).system_bound original id 0 _ M bounded),
    fun _ => ⟨id, basis_initial original⟩⟩

/-- The real pivot routine preserves the bounded-prefix invariant. Missing
pivots fail without arithmetic; a found pivot is nonzero after swapping,
so the defensive zero branch is unreachable. No nonsingularity of the
original system is assumed. -/
theorem pivotStep_runInvariant (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) (state : GaussianState q) (pivot : Fin q)
    (invariant : RunInvariant original M pivot.val state) :
    RunInvariant original M (pivot.val+1) (pivotStep state pivot) := by
  by_cases ok : state.ok = true
  · obtain ⟨permutation, basis⟩ := invariant.active_basis ok
    cases found : findPivot? state.system pivot with
    | none =>
        simp only [pivotStep, ok, if_true, found]
        exact ⟨invariant.safe.fail _ _ _, by simp [GaussianState.fail]⟩
    | some row =>
        obtain ⟨after, nonzero⟩ := findPivot?_some_property state.system pivot row found
        let swapped := state.emit (.swap pivot row)
        let nextPermutation := permutation ∘ Equiv.swap pivot row
        have swappedBasis : BasisInvariant original nextPermutation pivot.val swapped.system :=
          basis.swap original permutation pivot.val state.system pivot row (Nat.le_refl _) after
        have swappedSafe : SafeState (integralSystem original) (intermediateBound q M) swapped :=
          invariant.safe.emit _ _ _ (.swap pivot row) trivial
            (swappedBasis.system_bound original nextPermutation pivot.val swapped.system M bounded)
        have value : swapped.system.coeff pivot pivot = state.system.coeff row pivot := by
          simp [swapped, GaussianState.emit, applyRowOp, RowOp.transform]
        have pivotNonzero : swapped.system.coeff pivot pivot ≠ 0 := by rw [value]; exact nonzero
        have swappedOk : swapped.ok = true := ok
        let normalized := swapped.emit (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
        have normalizedSafe : SafeState (integralSystem original) (intermediateBound q M) normalized := by
          apply swappedSafe.emit _ _ _ (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
          · change rationalBits (swapped.system.coeff pivot pivot)⁻¹ ≤ intermediateBound q M
            rw [rationalBits_inv _ pivotNonzero]
            exact swappedSafe.current pivot (some pivot)
          · exact actual_partial_pivot_bound original nextPermutation swapped pivot [] swappedBasis
              swappedOk pivotNonzero M bounded
        let finished := eliminateRows pivot (List.finRange q) normalized
        have finishedSafe : SafeState (integralSystem original) (intermediateBound q M) finished :=
          eliminateRows_safe _ _ normalized pivot (List.finRange q) normalizedSafe
            (fun rows => actual_partial_pivot_bound original nextPermutation swapped pivot rows swappedBasis
              swappedOk pivotNonzero M bounded)
        have finishedBasis : BasisInvariant original nextPermutation (pivot.val+1) finished.system := by
          rw [show finished.system = pivotResult swapped.system pivot from actual_full_pivot swapped pivot swappedOk pivotNonzero]
          exact swappedBasis.pivot original nextPermutation swapped.system pivot pivotNonzero
        have actual : pivotStep state pivot = finished := by
          simp only [pivotStep, ok, if_true, found]
          change (if swapped.system.coeff pivot pivot = 0 then swapped.fail else finished) = finished
          exact if_neg pivotNonzero
        rw [actual]
        exact ⟨finishedSafe, fun _ => ⟨nextPermutation, finishedBasis⟩⟩
  · simp only [pivotStep, ok]
    exact ⟨invariant.safe, fun active => False.elim (ok active)⟩

theorem foldl_runInvariant (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) (pivots : List (Fin q)) (frontier : Nat)
    (consecutive : ConsecutiveFrom frontier pivots) (state : GaussianState q)
    (invariant : RunInvariant original M frontier state) :
    RunInvariant original M (frontier+pivots.length) (pivots.foldl pivotStep state) := by
  induction pivots generalizing frontier state with
  | nil => simpa only [List.length_nil, Nat.add_zero, List.foldl_nil] using invariant
  | cons pivot pivots ih =>
      obtain ⟨value, consecutiveTail⟩ := consecutiveFrom_cons consecutive
      have atPivot : RunInvariant original M pivot.val state := value.symm ▸ invariant
      have next := pivotStep_runInvariant original M bounded state pivot atPivot
      rw [value] at next
      have tail := ih (frontier+1) consecutiveTail (pivotStep state pivot) next
      simpa only [List.length_cons, List.foldl_cons, Nat.add_assoc, Nat.add_comm 1] using tail

/-- Every generator intermediate and every replay prefix has polynomial
bit length, whether the solver succeeds or stops at a singular frontier. -/
theorem runGaussian_safe (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) :
    SafeState (integralSystem original) (intermediateBound q M) (runGaussian (integralSystem original)) :=
  (foldl_runInvariant original M bounded (List.finRange q) 0 consecutiveFrom_finRange _
    (runInvariant_initial original M bounded)).safe

theorem storedGaussian_replay_prefix_bits (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) (length : Nat) (row : Fin q) (column : Option (Fin q)) :
    rationalBits (augmented (StoredGaussian.replay (integralSystem original)
      ((StoredGaussian.runGaussian (integralSystem original)).opsRev.reverse.take length)) row column) ≤
        intermediateBound q M := by
  rw [StoredGaussian.runGaussian_eq, StoredGaussian.replay_eq]
  exact (runGaussian_safe original M bounded).prefixes length row column

theorem storedGaussian_operation_bits (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c, (original i c).natAbs ≤ M) (op : RowOp q)
    (emitted : op ∈ (StoredGaussian.runGaussian (integralSystem original)).opsRev) :
    OperationBound (intermediateBound q M) op := by
  rw [StoredGaussian.runGaussian_eq] at emitted
  exact (runGaussian_safe original M bounded).operations op emitted

end Counting.GaussianBits
