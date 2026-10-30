import Counting.StackGaussianCostBounds
import Counting.StackGaussianInput

namespace Counting.StackMachine.GaussianBank
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem GaussianBits
open DirectedCounting.GaussianGeneratorCompleteness
set_option maxRecDepth 10000

private theorem eliminateCount_as_rows {q : Nat} (pivot : Fin q) (start count : Nat) (state : GaussianState q) :
    ∃ rows : List (Fin q),StoredGaussian.eliminateCount pivot start count state=
      StoredGaussian.eliminateRows pivot rows state := by
  induction count generalizing start state with
  | zero => exact ⟨[],rfl⟩
  | succ count ih =>
    obtain ⟨rows,tail⟩ := ih (start+1) (StoredGaussian.eliminateAt pivot state start)
    change StoredGaussian.eliminateCount pivot (start+1) count (StoredGaussian.eliminateAt pivot state start)=_ at tail
    by_cases inside : start<q
    · let row : Fin q := ⟨start,inside⟩
      refine ⟨row::rows,?_⟩
      simpa only [StoredGaussian.eliminateCount,StoredGaussian.eliminateAt,inside,↓reduceDIte,
        StoredGaussian.eliminateRows,List.foldl_cons,row] using tail
    · refine ⟨rows,?_⟩
      simpa only [StoredGaussian.eliminateCount,StoredGaussian.eliminateAt,inside,↓reduceDIte] using tail

theorem successfulCost_bound {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) (state : GaussianState q) (pivot row : Fin q)
    (invariant : RunInvariant original M pivot.val state) (active : state.ok=true)
    (found : findPivot? state.system pivot=some row) :
    successfulCost state pivot row ≤ successBudget q (intermediateBound q M) := by
  obtain ⟨permutation,basis⟩ := invariant.active_basis active
  have rowProperty := findPivot?_some_property state.system pivot row found
  let swapped := StoredGaussian.emit state (.swap pivot row)
  let nextPermutation := permutation ∘ Equiv.swap pivot row
  have swappedBasis : BasisInvariant original nextPermutation pivot.val swapped.system := by
    simpa only [swapped,StoredGaussian.emit_eq,GaussianState.emit,nextPermutation] using
      basis.swap original permutation pivot.val state.system pivot row (Nat.le_refl _) rowProperty.1
  have swappedBound := swappedBasis.system_bound original nextPermutation pivot.val swapped.system M bounded
  have value : swapped.system.coeff pivot pivot=state.system.coeff row pivot := swapped_pivot_value state pivot row
  have nonzero : swapped.system.coeff pivot pivot≠0 := by rw [value];exact rowProperty.2
  have swappedActive : swapped.ok=true := active
  have prefixBound : ∀ k ≤ q,SystemBound (intermediateBound q M)
      (StoredGaussian.eliminateCount pivot 0 k (normalizedState state pivot row)).system := by
    intro k _
    obtain ⟨rows,equal⟩ := eliminateCount_as_rows pivot 0 k (normalizedState state pivot row)
    rw [equal]
    have bound := actual_partial_pivot_bound original nextPermutation swapped pivot rows
      swappedBasis swappedActive nonzero M bounded
    simpa only [StoredGaussian.eliminateRows_eq,normalizedState,StoredGaussian.emit_eq,swapped] using bound
  have rowsBound := rowsCost_bound pivot 0 q (normalizedState state pivot row)
    (intermediateBound q M) (by omega) prefixBound
  have allBound : allRowsCost (normalizedState state pivot row) pivot ≤ allRowsBudget q (intermediateBound q M) := by
    dsimp only [allRowsCost,allRowsBudget]
    omega
  have swapBound := recordedSwapCost_bound state.system pivot row (intermediateBound q M) invariant.safe.current
  have scaleBound := recordedScaleCost_bound swapped.system pivot (intermediateBound q M) swappedBound
  dsimp only [successfulCost,successBudget]
  gcongr
  exact Nat.le_of_lt row.isLt

theorem pivotStepCost_bound {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) (state : GaussianState q) (pivot : Fin q)
    (invariant : RunInvariant original M pivot.val state) :
    pivotStepCost state pivot ≤ pivotBudget q (intermediateBound q M) := by
  have matrix := augmentedMatrix_encoded_bound state.system (intermediateBound q M) invariant.safe.current
  change _ ≤ matrixBudget q (intermediateBound q M) at matrix
  have searchBound : searchCost state ≤ 50000*(matrixBudget q (intermediateBound q M)+q+1)^2 := by
    dsimp only [searchCost]
    gcongr
  cases active : state.ok with
  | false => simp only [pivotStepCost,active,Bool.false_eq_true,if_false,pivotBudget];omega
  | true =>
    cases found : findPivot? state.system pivot with
    | none =>
      simp only [pivotStepCost,active,if_true,activePivotCost,foundCost,found,pivotBudget]
      omega
    | some row =>
      have succeeded := successfulCost_bound original M bounded state pivot row invariant active found
      simp only [pivotStepCost,active,if_true,activePivotCost,foundCost,found,pivotBudget]
      omega

theorem pivotsCost_bound {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) (start count : Nat) (state : GaussianState q)
    (invariant : RunInvariant original M start state) (inside : start+count ≤ q) :
    pivotsCost start count state ≤ count*(pivotBudget q (intermediateBound q M)+4)+1 := by
  induction count generalizing start state with
  | zero => simp [pivotsCost]
  | succ count ih =>
    let pivot : Fin q := ⟨start,by omega⟩
    have head := pivotStepCost_bound original M bounded state pivot invariant
    have nextInvariant : RunInvariant original M (start+1) (StoredGaussian.pivotAt state start) := by
      have next := pivotStep_runInvariant original M bounded state pivot invariant
      simpa only [←StoredGaussian.pivotStep_eq,←StoredGaussian.pivotAt_fin] using next
    have tail := ih (start+1) (StoredGaussian.pivotAt state start) nextInvariant (by omega)
    have costAt : pivotCostAt state start=pivotStepCost state pivot := by simp [pivotCostAt,pivot.isLt,pivot]
    simp only [pivotsCost,costAt,Nat.add_mul,Nat.one_mul]
    omega

def generatorBudget (q bits : Nat) : Nat :=
  2000*(matrixBudget q bits+1)^3+1+(5*q+3+(q*(pivotBudget q bits+4)+1))

/-- A uniform polynomial expression in dimension and the proven intermediate
bit bound controls the actual generated finite-state execution. -/
theorem generateInput_integral {q : Nat} (original : Augmented q ℤ) (M : Nat)
    (bounded : ∀ i c,(original i c).natAbs ≤ M) :
    ∃ time ≤ generatorBudget q (intermediateBound q M),
      Routine.Executes generateInput
        (inputFile (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (integralSystem original))) [] [] [] []) time
        (outerStore (StoredGaussian.runGaussian (integralSystem original)) q []) := by
  have invariant := runInvariant_initial original M bounded
  have matrix := augmentedMatrix_encoded_bound (integralSystem original) (intermediateBound q M) invariant.safe.current
  change _ ≤ matrixBudget q (intermediateBound q M) at matrix
  have costs := pivotsCost_bound original M bounded 0 q ⟨integralSystem original,[],true⟩ invariant (by omega)
  obtain ⟨time,timeBound,ran⟩ := generateInput_executes (integralSystem original)
  refine ⟨time,timeBound.trans ?_,ran⟩
  dsimp only [generatorBudget]
  gcongr

end Counting.StackMachine.GaussianBank
