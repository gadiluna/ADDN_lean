import Counting.StackGaussianBank
import Counting.StackGaussianPivotCorrectness

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

def searchSaved (saved : Fin 10 → List Bool) (candidate counter active : List Bool) : Fin 10 → List Bool :=
  Function.update (Function.update (Function.update saved 2 candidate) 7 counter) 8 active

def searchStore (matrix candidate column counter active : List Bool) (saved : Fin 10 → List Bool) : Fin 52 → List Bool :=
  ready matrix [] [] column (searchSaved saved candidate counter active)

def searchRoles : Fin 31 ↪ Fin 52 :=
  ⟨![37,44,39,1,0,40,41,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,49,50],by decide⟩

abbrev searchLoop : Routine 50 := relocate GaussianPivot.loop searchRoles

theorem searchLoop_executes (rows : List (List Rat)) (column : Nat) (value : Nat → Rat)
    (entries : ∀ row : Fin rows.length, rows[row.val][column]?=some (value row.val))
    (count start : Nat) (inside : start+count ≤ rows.length) (saved : Fin 10 → List Bool) :
    ∃ time ≤ count*(5000*((Encoding.rationalMatrix.encode rows).length+rows.length+column+count+7)+2)+1,
      Executes searchLoop
        (searchStore (Encoding.rationalMatrix.encode rows) (List.replicate (start+1) true)
          (List.replicate (column+1) true) (List.replicate count true) [true] saved) time
        (searchStore (Encoding.rationalMatrix.encode rows)
          (List.replicate ((GaussianPivot.search value count start).1+1) true)
          (List.replicate (column+1) true) [] [(GaussianPivot.search value count start).2] saved) := by
  obtain ⟨time,bounded,ran⟩ := GaussianPivot.loop_executes rows column value entries count start inside
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianPivot.loop searchRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [searchStore,searchSaved,ready,bank,searchRoles,
      MatrixAxpy.file,RowAxpy.file,GaussianPivot.state,GaussianPivot.file]
  · intro r;fin_cases r <;> simp [searchStore,searchSaved,ready,bank,searchRoles,
      MatrixAxpy.file,RowAxpy.file,GaussianPivot.state,GaussianPivot.file]
  · intro r outside
    have candidate := outside 1
    have counter := outside 29
    have active := outside 30
    fin_cases r <;> simp_all [searchStore,searchSaved,ready,bank,searchRoles,MatrixAxpy.file,RowAxpy.file]

theorem searchLoop_augmented {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (saved : Fin 10 → List Bool) :
    ∃ time result exhausted,
      time ≤ (q-pivot.val)*(5000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+
        q+pivot.val+(q-pivot.val)+7)+2)+1 ∧
      Executes searchLoop
        (searchStore (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system))
          (List.replicate (pivot.val+1) true) (List.replicate (pivot.val+1) true)
          (List.replicate (q-pivot.val) true) [true] saved) time
        (searchStore (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system))
          (List.replicate (result+1) true) (List.replicate (pivot.val+1) true) [] [exhausted] saved) ∧
      (if exhausted then none else some result)=(findPivot? system pivot).map Fin.val := by
  obtain ⟨time,bounded,ran⟩ := searchLoop_executes (StoredGaussian.augmentedMatrix system) pivot.val
    (GaussianPivot.columnValue system pivot) (GaussianPivot.augmented_entries system pivot)
    (q-pivot.val) pivot.val (by simp) saved
  exact ⟨time,_,_,by simpa using bounded,ran,GaussianPivot.searchResult_findPivot system pivot⟩

end Counting.StackMachine.GaussianBank
