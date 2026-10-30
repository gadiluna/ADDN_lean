import Counting.StackGaussianRecordedAdd
import Counting.StackGaussianControl

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

abbrev rowStep : Routine 50 := sequence compareRow
  (branchRead 50 (clear 50) (sequence (clear 50) eliminateRecorded))

def rowStepCost {q : Nat} (system : RationalSystem q) (pivot row : Fin q) : Nat :=
  Compare.preservingCost (List.replicate (pivot.val+1) true) (List.replicate (row.val+1) true)+
    recordedAddCost system row pivot+7

theorem clearStateFlag_executes {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter : List Bool) (flag : Bool) :
    Executes (clear (50 : Fin 52)) (stateStore state pivot candidate row counter [flag]) 2
      (stateStore state pivot candidate row counter []) := by
  have ran := clearSaved_executes 8 (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)) [] [] []
    (stateSaved state pivot candidate row counter [flag])
  have updated : Function.update (stateSaved state pivot candidate row counter [flag]) 8 []=
      stateSaved state pivot candidate row counter [] := by
    funext r;fin_cases r <;> simp [stateSaved]
  rw [updated] at ran
  exact ran

/-- The finite body tests the actual serialized unary indices, skips only
the pivot row, and otherwise emits the exact stored row addition. -/
theorem rowStep_executes {q : Nat} (state : GaussianState q) (pivot row : Fin q)
    (active : state.ok=true) (counter : List Bool) :
    ∃ time ≤ rowStepCost state.system pivot row,
      Executes rowStep (stateStore state pivot.val [] (List.replicate (row.val+1) true) counter []) time
        (stateStore (StoredGaussian.eliminateOne pivot state row) pivot.val [] (List.replicate (row.val+1) true) counter []) := by
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)
  let rowCode := List.replicate (row.val+1) true
  let pivotCode := List.replicate (pivot.val+1) true
  let saved := stateSaved state pivot.val [] rowCode counter []
  have compared := compareRow_executes matrix saved rfl
  have sameWords : pivotCode=rowCode ↔ row=pivot := by
    constructor
    · intro equal
      have lengths := congrArg List.length equal
      simp only [pivotCode,rowCode,List.length_replicate] at lengths
      apply Fin.ext;omega
    · intro equal;subst row;rfl
  have sameDecision : decide (pivotCode=rowCode)=decide (row=pivot) := by
    exact decide_eq_decide.mpr sameWords
  have comparisonResult : ready matrix [] [] [] (Function.update saved 8 [decide (saved 0=saved 6)])=
      stateStore state pivot.val [] rowCode counter [decide (row=pivot)] := by
    funext r;fin_cases r <;> simp [saved,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,
      ←sameDecision,pivotCode,rowCode,matrix]
  rw [comparisonResult] at compared
  change Executes compareRow (stateStore state pivot.val [] rowCode counter [])
    (Compare.preservingCost pivotCode rowCode) (stateStore state pivot.val [] rowCode counter [decide (row=pivot)]) at compared
  by_cases same : row=pivot
  · have cleared := clearStateFlag_executes state pivot.val [] rowCode counter true
    have selected : Executes (if true then clear (50 : Fin 52) else sequence (clear 50) eliminateRecorded)
        (stateStore state pivot.val [] rowCode counter [true]) 2 (stateStore state pivot.val [] rowCode counter []) := cleared
    have branch := branchRead_executes (50 : Fin 52) (clear 50) (sequence (clear 50) eliminateRecorded)
      true [] _ _ 2 rfl selected
    simp only [same,decide_true] at compared
    have result : StoredGaussian.eliminateOne pivot state row=state := by simp [StoredGaussian.eliminateOne,active,same]
    rw [result]
    refine ⟨_,?_,compared.sequence branch⟩
    change Compare.preservingCost pivotCode rowCode+1+(2+3) ≤
      Compare.preservingCost pivotCode rowCode+recordedAddCost state.system row pivot+7
    exact Nat.le_trans (by omega : Compare.preservingCost pivotCode rowCode+1+(2+3) ≤
      Compare.preservingCost pivotCode rowCode+7)
      (by omega)
  · obtain ⟨time,bounded,ran⟩ := eliminateRecorded_executes state row pivot counter
    have cleared := clearStateFlag_executes state pivot.val [] rowCode counter false
    have selected : Executes (sequence (clear (50 : Fin 52)) eliminateRecorded)
        (stateStore state pivot.val [] rowCode counter [false]) (2+1+time)
        (stateStore (StoredGaussian.emit state (.add row pivot (-state.system.coeff row pivot))) pivot.val [] rowCode counter []) :=
      cleared.sequence ran
    have branch := branchRead_executes (50 : Fin 52) (clear 50) (sequence (clear 50) eliminateRecorded)
      false [] _ _ (2+1+time) rfl (by simpa only [Bool.false_eq_true,if_false] using selected)
    simp only [same,decide_false] at compared
    have result : StoredGaussian.eliminateOne pivot state row=StoredGaussian.emit state (.add row pivot (-state.system.coeff row pivot)) := by
      simp [StoredGaussian.eliminateOne,active,same]
    rw [result]
    refine ⟨_,?_,compared.sequence branch⟩
    dsimp only [rowStepCost]
    change Compare.preservingCost pivotCode rowCode+1+(2+1+time+3) ≤
      Compare.preservingCost pivotCode rowCode+recordedAddCost state.system row pivot+7
    omega

end Counting.StackMachine.GaussianBank
