import Counting.StackGaussianFind
import Counting.StackGaussianSuccess

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev activePivot : Routine 50 := sequence findPivot (branchRead 50 failSearch successfulPivot)
abbrev pivotStepRoutine : Routine 50 := branchRead 45 activePivot (skip 50)

def searchCost {q : Nat} (state : GaussianState q) : Nat :=
  50000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)).length+q+1)^2

def foundCost {q : Nat} (state : GaussianState q) (pivot : Fin q) : Nat :=
  match findPivot? state.system pivot with
  | none => q+10
  | some row => successfulCost state pivot row

def activePivotCost {q : Nat} (state : GaussianState q) (pivot : Fin q) : Nat :=
  searchCost state+1+(foundCost state pivot+3)

def pivotStepCost {q : Nat} (state : GaussianState q) (pivot : Fin q) : Nat :=
  if state.ok then activePivotCost state pivot+3 else 3

theorem activePivot_executes {q : Nat} (state : GaussianState q) (pivot : Fin q)
    (active : state.ok=true) :
    ∃ time ≤ activePivotCost state pivot,
      Executes activePivot (stateStore state pivot.val [] [] [] []) time
        (stateStore (StoredGaussian.pivotStep state pivot) pivot.val [] [] [] []) := by
  obtain ⟨searchTime,result,exhausted,searchBound,indexBound,searched,correct⟩ :=
    findPivot_bounded_executes state.system pivot (stateSaved state pivot.val [] [] [] []) rfl rfl
  simp only [searchSaved_stateSaved] at searched
  change Executes findPivot (stateStore state pivot.val [] [] [] []) searchTime
    (stateStore state pivot.val (List.replicate (result+1) true) [] [] [exhausted]) at searched
  cases exhausted with
  | true =>
    have missing : findPivot? state.system pivot=none := by
      cases choice : findPivot? state.system pivot with
      | none => rfl
      | some row => simp [choice] at correct
    have failed := failSearch_executes state pivot.val result
    have chosen : Executes (if true then failSearch else successfulPivot)
        (stateStore state pivot.val (List.replicate (result+1) true) [] [] [true]) (result+10)
        (stateStore state.fail pivot.val [] [] [] []) := failed
    have branch := branchRead_executes (50 : Fin 52) failSearch successfulPivot true [] _ _ (result+10) rfl chosen
    have final : StoredGaussian.pivotStep state pivot=state.fail := by simp [StoredGaussian.pivotStep,active,missing]
    rw [final]
    refine ⟨_,?_,searched.sequence branch⟩
    simp only [activePivotCost,foundCost,missing]
    exact Nat.add_le_add (Nat.add_le_add_right searchBound 1) (by omega)
  | false =>
    cases found : findPivot? state.system pivot with
    | none => simp [found] at correct
    | some row =>
      have equal : result=row.val := by simpa [found] using correct
      subst result
      obtain ⟨successTime,successBound,succeeded⟩ := successfulPivot_executes state pivot row active found
      have branch := branchRead_executes (50 : Fin 52) failSearch successfulPivot false [] _ _ successTime rfl
        (by simpa only [Bool.false_eq_true,if_false] using succeeded)
      refine ⟨_,?_,searched.sequence branch⟩
      simp only [activePivotCost,foundCost,found]
      exact Nat.add_le_add (Nat.add_le_add_right searchBound 1) (Nat.add_le_add_right successBound 3)

/-- One actual finite-state solver step implements every field of the
materialized Gaussian pivot operation, including failure and inactive
states. No matrix dimension or operation transcript is an oracle. -/
theorem pivotStep_executes {q : Nat} (state : GaussianState q) (pivot : Fin q) :
    ∃ time ≤ pivotStepCost state pivot,
      Executes pivotStepRoutine (stateStore state pivot.val [] [] [] []) time
        (stateStore (StoredGaussian.pivotStep state pivot) pivot.val [] [] [] []) := by
  cases active : state.ok with
  | false =>
    have unchanged : StoredGaussian.pivotStep state pivot=state := by simp [StoredGaussian.pivotStep,active]
    have ran := skip_executes (stateStore state pivot.val [] [] [] [])
    have branch := branchRead_executes (45 : Fin 52) activePivot (skip 50) false []
      (stateStore state pivot.val [] [] [] []) (stateStore state pivot.val [] [] [] []) 0
      (by simp [stateStore,stateSaved,ready,bank,active])
      (by simpa only [Bool.false_eq_true,if_false] using ran)
    refine ⟨3,?_,?_⟩
    · simp [pivotStepCost,active]
    · simpa only [unchanged] using branch
  | true =>
    obtain ⟨time,bounded,ran⟩ := activePivot_executes state pivot active
    have branch := branchRead_executes (45 : Fin 52) activePivot (skip 50) true []
      (stateStore state pivot.val [] [] [] [])
      (stateStore (StoredGaussian.pivotStep state pivot) pivot.val [] [] [] []) time
      (by simp [stateStore,stateSaved,ready,bank,active]) (by simpa only [if_true] using ran)
    refine ⟨time+3,?_,branch⟩
    simp only [pivotStepCost,active,if_true]
    omega

end Counting.StackMachine.GaussianBank
