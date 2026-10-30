import Counting.StoredGaussian

/-! The actual successful Gaussian run already contains the returned vector.
The generated transcript remains certified, but it need not be executed a
second time merely to extract the same solution. -/
namespace Counting.GaussianDirectSolve
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
open DirectedCounting.GaussianGeneratorCompleteness
variable {q : Nat}

theorem pivotStep_processed (state : GaussianState q) (pivot : Fin q)
    (processed : state.ok=true → ProcessedColumns state.system.coeff pivot.val)
    (success : (pivotStep state pivot).ok=true) :
    ProcessedColumns (pivotStep state pivot).system.coeff (pivot.val+1) := by
  by_cases active : state.ok=true
  · have previous := processed active
    cases found : findPivot? state.system pivot with
    | none => simp [pivotStep,active,found,GaussianState.fail] at success
    | some row =>
      have rowProperty := findPivot?_some_property state.system pivot row found
      let swapped := state.emit (.swap pivot row)
      have swappedValue : swapped.system.coeff pivot pivot=state.system.coeff row pivot := by
        simp [swapped,GaussianState.emit,applyRowOp,RowOp.transform]
      have nonzero : swapped.system.coeff pivot pivot ≠ 0 := by
        rw [swappedValue]
        exact rowProperty.2
      have swappedProcessed : ProcessedColumns swapped.system.coeff pivot.val := by
        simpa only [swapped,GaussianState.emit] using
          processedColumns_apply_swap state.system previous pivot row (Nat.le_refl _) rowProperty.1
      let normalized := swapped.emit (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
      have normalizedOk : normalized.ok=true := active
      have normalizedProcessed : ProcessedColumns normalized.system.coeff pivot.val := by
        simpa only [normalized,GaussianState.emit] using
          processedColumns_apply_scale swapped.system swappedProcessed pivot (Nat.le_refl _)
            (swapped.system.coeff pivot pivot)⁻¹
      have normalizedPivot : normalized.system.coeff pivot pivot=1 := by
        simp [normalized,GaussianState.emit,applyRowOp,RowOp.transform,nonzero]
      let next := eliminateRows pivot (List.finRange q) normalized
      have nextProcessed : ProcessedColumns next.system.coeff pivot.val :=
        eliminateRows_processedColumns pivot (List.finRange q) normalized (Nat.le_refl _) normalizedProcessed
      have nextColumn : ∀ r : Fin q,next.system.coeff r pivot=if r=pivot then 1 else 0 :=
        eliminateRows_finRange_pivot_column pivot normalized normalizedOk normalizedPivot
      have same : pivotStep state pivot=next := by
        simp [pivotStep,active,found,swapped,nonzero,normalized,next]
      rw [same]
      exact processedColumns_succ_of_pivot_column next.system.coeff pivot nextProcessed nextColumn
  · simp [pivotStep,active] at success

theorem fold_processed (pivots : List (Fin q)) (k : Nat)
    (consecutive : ConsecutiveFrom k pivots) (state : GaussianState q)
    (processed : state.ok=true → ProcessedColumns state.system.coeff k)
    (success : (pivots.foldl pivotStep state).ok=true) :
    ProcessedColumns (pivots.foldl pivotStep state).system.coeff (k+pivots.length) := by
  induction pivots generalizing k state with
  | nil => simpa only [List.foldl_nil,List.length_nil,Nat.add_zero] using processed success
  | cons pivot rest ih =>
    obtain ⟨value,remaining⟩ := consecutiveFrom_cons consecutive
    have nextProcessed : (pivotStep state pivot).ok=true →
        ProcessedColumns (pivotStep state pivot).system.coeff (k+1) := by
      intro ok
      have initial : state.ok=true → ProcessedColumns state.system.coeff pivot.val := by
        simpa only [value] using processed
      simpa only [value] using pivotStep_processed state pivot initial ok
    have result := ih (k+1) remaining (pivotStep state pivot) nextProcessed success
    simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

theorem runGaussian_coeff_eq_one_of_ok (system : RationalSystem q)
    (success : (runGaussian system).ok=true) : (runGaussian system).system.coeff=1 := by
  apply processedColumns_full_eq_one
  have result := fold_processed (List.finRange q) 0 consecutiveFrom_finRange
    ({system:=system,opsRev:=[],ok:=true} : GaussianState q)
    (by intro _ col before;omega) success
  simpa only [runGaussian,List.length_finRange,Nat.zero_add] using result

end Counting.GaussianDirectSolve

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver
open DirectedCounting.GaussianGeneratorCompleteness
variable {q : Nat}

/-- Exact equality for every square system, including singular and failed
runs. The input need not satisfy an anchor invariant or be nonsingular. -/
theorem solve_eq_direct (system : RationalSystem q) :
    solve? system=if (runGaussian system).ok then some (runGaussian system).system.rhs else none := by
  rw [solve?]
  split_ifs with success
  · rw [verifyTranscript_eq,runGaussian_eq]
    have active : (RationalSystem.runGaussian system).ok=true := by
      simpa only [runGaussian_eq] using success
    have identity := GaussianDirectSolve.runGaussian_coeff_eq_one_of_ok system active
    have certified := runGaussian_stateCertified system
    simp only [RationalSystem.verifyTranscript,certified.1,certified.2,identity,and_self,if_true]
  · rfl

end Counting.StoredGaussian
