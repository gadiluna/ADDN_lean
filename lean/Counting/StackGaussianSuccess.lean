import Counting.StackGaussianRows
import Counting.StackGaussianRecordedPivot

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

abbrev successfulPivot : Routine 50 := sequence (clear 50)
  (sequence swapRecorded (sequence (clear 44) (sequence normalizeRecorded eliminateAll)))

def normalizedState {q : Nat} (state : GaussianState q) (pivot row : Fin q) : GaussianState q :=
  let swapped := StoredGaussian.emit state (.swap pivot row)
  StoredGaussian.emit swapped (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)

def allRowsCost {q : Nat} (state : GaussianState q) (pivot : Fin q) : Nat :=
  5*q+4+1+(rowsCost pivot 0 q state+1+(q+2))

def successfulCost {q : Nat} (state : GaussianState q) (pivot row : Fin q) : Nat :=
  let swapped := StoredGaussian.emit state (.swap pivot row)
  2+1+(recordedSwapCost state.system pivot row+1+
    (row.val+2+1+(recordedScaleCost swapped.system pivot+1+allRowsCost (normalizedState state pivot row) pivot)))

theorem clearCandidate_executes {q : Nat} (state : GaussianState q) (pivot : Nat) (candidate : List Bool) :
    Executes (clear (44 : Fin 52)) (stateStore state pivot candidate [] [] []) (candidate.length+1)
      (stateStore state pivot [] [] [] []) := by
  have ran := clearSaved_executes 2 (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)) [] [] []
    (stateSaved state pivot candidate [] [] [])
  have updated : Function.update (stateSaved state pivot candidate [] [] []) 2 []=stateSaved state pivot [] [] [] [] := by
    funext r;fin_cases r <;> simp [stateSaved]
  rw [updated] at ran
  exact ran

/-- Successful branch of one complete stored pivot: the selected swap,
computed reciprocal, row scaling, all off-diagonal additions, and every
transcript entry are produced by finite executable routines. -/
theorem successfulPivot_executes {q : Nat} (state : GaussianState q) (pivot row : Fin q)
    (active : state.ok=true) (found : findPivot? state.system pivot=some row) :
    ∃ time ≤ successfulCost state pivot row,
      Executes successfulPivot (stateStore state pivot.val (List.replicate (row.val+1) true) [] [] [false]) time
        (stateStore (StoredGaussian.pivotStep state pivot) pivot.val [] [] [] []) := by
  let swapped := StoredGaussian.emit state (.swap pivot row)
  let scaled := normalizedState state pivot row
  have a := clearStateFlag_executes state pivot.val (List.replicate (row.val+1) true) [] [] false
  obtain ⟨swapTime,swapBound,swappedRun⟩ := swapRecorded_executes state pivot row
  have c := clearCandidate_executes swapped pivot.val (List.replicate (row.val+1) true)
  simp only [List.length_replicate] at c
  obtain ⟨scaleTime,scaleBound,scaledRun⟩ := normalizeRecorded_executes swapped pivot [] [] []
  have scaledActive : scaled.ok=true := by simp [scaled,normalizedState,StoredGaussian.emit,active]
  obtain ⟨rowsTime,rowsBound,rowsRun⟩ := eliminateAll_executes scaled pivot scaledActive
  have final : StoredGaussian.eliminateRows pivot (List.finRange q) scaled=StoredGaussian.pivotStep state pivot := by
    rw [pivotStep_of_found state pivot row active found]
    dsimp only [scaled,normalizedState]
    rw [swapped_pivot_value]
  rw [final] at rowsRun
  have composed := a.sequence (swappedRun.sequence (c.sequence (scaledRun.sequence rowsRun)))
  refine ⟨_,?_,composed⟩
  unfold successfulCost
  exact Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right swapBound 1)
    (Nat.add_le_add_left (Nat.add_le_add (Nat.add_le_add_right scaleBound 1) rowsBound) _)) _

end Counting.StackMachine.GaussianBank
