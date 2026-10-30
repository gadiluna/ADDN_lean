import Counting.StackGaussianPivotLoop
import Counting.MachineMatrixSwapGaussian

namespace Counting.StackMachine.GaussianPivot
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem Routine

def searchResult (value : Nat → Rat) (count start : Nat) : Option Nat :=
  if (search value count start).2 then none else some (search value count start).1

theorem searchResult_find (value : Nat → Rat) (count start : Nat) :
    searchResult value count start=(List.range' start count).find? (fun row=>decide (value row≠0)) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    by_cases zero : value start=0
    · simpa [searchResult,search,zero,List.range'_succ] using ih (start+1)
    · simp [searchResult,search,zero,List.range'_succ]

/-- Extend a physical coefficient column only to state the natural-index
search specification. The machine never accesses an index outside the matrix. -/
def columnValue {q : Nat} (system : RationalSystem q) (column : Fin q) (row : Nat) : Rat :=
  if bounded : row<q then system.coeff ⟨row,bounded⟩ column else 0

@[simp] theorem columnValue_fin {q : Nat} (system : RationalSystem q) (column row : Fin q) :
    columnValue system column row.val=system.coeff row column := by simp [columnValue,row.isLt]

private theorem map_finRange_val (q : Nat) : (List.finRange q).map Fin.val=List.range q := by
  apply List.ext_getElem (by simp)
  intro i leftBound rightBound
  simp

private theorem range_find_from (value : Nat → Rat) (q start : Nat) (bounded : start≤q) :
    (List.range q).find? (fun row=>decide (start≤row ∧ value row≠0))=
      (List.range' start (q-start)).find? (fun row=>decide (value row≠0)) := by
  have split : List.range q=List.range start++List.range' start (q-start) := by
    simpa only [List.range_eq_range',Nat.zero_add,Nat.add_sub_of_le bounded] using
      (List.range'_append_1 (s:=0) (m:=start) (n:=q-start)).symm
  rw [split,List.find?_append]
  have noEarlier : (List.range start).find? (fun row=>decide (start≤row ∧ value row≠0))=none := by
    rw [List.find?_eq_none]
    intro row member
    have lower := List.mem_range.mp member
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_and]
    omega
  rw [noEarlier,Option.none_or]
  apply List.find?_congr
  intro row member
  obtain ⟨offset,_,equal⟩ := List.mem_range'.mp member
  have lower : start≤row := by omega
  simp [lower]

/-- The first candidate chosen by the finite loop is exactly the pivot
chosen by the actual Gaussian implementation, including failure. -/
theorem searchResult_findPivot {q : Nat} (system : RationalSystem q) (pivot : Fin q) :
    searchResult (columnValue system pivot) (q-pivot.val) pivot.val=
      (findPivot? system pivot).map Fin.val := by
  rw [searchResult_find,← range_find_from _ q pivot.val (Nat.le_of_lt pivot.isLt)]
  rw [← map_finRange_val,List.find?_map]
  congr 1
  apply List.find?_congr
  intro row _
  simp [columnValue_fin]

theorem augmented_entries {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (row : Fin (StoredGaussian.augmentedMatrix system).length) :
    (StoredGaussian.augmentedMatrix system)[row.val][pivot.val]?=
      some (columnValue system pivot row.val) := by
  have bounded : row.val<q := by simpa using row.isLt
  simp [StoredGaussian.augmentedMatrix,StoredGaussian.augmentedRow,columnValue,bounded,
    pivot.isLt]

/-- Internal reusable routine contract: the matrix, diagonal index, and
remaining candidate count are supplied as explicit register contents. This
statement charges the search; it does not treat preparing those counters as free. -/
theorem findPivot_executes {q : Nat} (system : RationalSystem q) (pivot : Fin q) :
    ∃ time result exhausted,
      time ≤ (q-pivot.val)*(5000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+
        q+pivot.val+(q-pivot.val)+7)+2)+1 ∧
      Executes loop (state (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system))
        pivot.val pivot.val (List.replicate (q-pivot.val) true) true) time
        (state (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) result pivot.val [] exhausted) ∧
      (if exhausted then none else some result)=(findPivot? system pivot).map Fin.val := by
  obtain ⟨time,bounded,ran⟩ := loop_executes (StoredGaussian.augmentedMatrix system) pivot.val
    (columnValue system pivot) (augmented_entries system pivot) (q-pivot.val) pivot.val
    (by simp)
  exact ⟨time,_,_,by simpa using bounded,ran,searchResult_findPivot system pivot⟩

end Counting.StackMachine.GaussianPivot
