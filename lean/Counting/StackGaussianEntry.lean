import Counting.StackGaussianCoefficient
import Counting.StackMatrixSwapBounds

namespace Counting.StackMachine.GaussianEntry
open Routine FieldAccess

def file (matrix rowIndex columnIndex row coefficient rowPresent coefficientPresent zero : List Bool) : Fin 29 → List Bool :=
  ![matrix,rowIndex,columnIndex,row,coefficient,rowPresent,coefficientPresent,zero,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def rowRoles : Fin 8 ↪ Fin 29 := ⟨![0,1,3,5,8,9,10,11],by decide⟩
def coefficientRoles : Fin 26 ↪ Fin 29 := ⟨![3,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],by decide⟩
abbrev readRow : Routine 27 := preservingRead 21 rowRoles
abbrev inspectRow : Routine 27 := relocate GaussianCoefficient.inspect coefficientRoles
abbrev inspect : Routine 27 := sequence readRow inspectRow

theorem readRow_executes (rows : List (List Rat)) (row : Fin rows.length) (columnIndex : List Bool) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(row.val+1)+14,
      Executes readRow (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true) columnIndex [] [] [] [] []) time
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true) columnIndex
          (Encoding.rationalRow.encode rows[row.val]) [] [true] [] []) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 21 rowRoles
    (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true) columnIndex [] [] [] [] [])
    rows row.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,rowRoles,row.isLt]

theorem inspectRow_executes (matrix rowIndex : List Bool) (row : List Rat) (column : Nat) (value : Rat)
    (selected : row[column]?=some value) :
    ∃ time ≤ 3000*((Encoding.rationalRow.encode row).length+column+2),
      Executes inspectRow (file matrix rowIndex (List.replicate (column+1) true)
        (Encoding.rationalRow.encode row) [] [true] [] []) time
        (file matrix rowIndex (List.replicate (column+1) true)
          (Encoding.rationalRow.encode row) (Encoding.rational.encode value) [true] [true] [decide (value=0)]) := by
  obtain ⟨time,bounded,ran⟩ := GaussianCoefficient.inspect_executes row column value selected
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianCoefficient.inspect coefficientRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,GaussianCoefficient.file,coefficientRoles]
  · intro r; fin_cases r <;> simp [file,GaussianCoefficient.file,coefficientRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · exact False.elim (outside 2 rfl)
    · simp [file]
    · exact False.elim (outside 3 rfl)
    · exact False.elim (outside 4 rfl)
    all_goals simp [file]

/-- Fetch a serialized matrix row and one of its coefficients, then execute
the rational zero test. Matrix and both explicit unary indices survive. -/
theorem inspect_executes (rows : List (List Rat)) (row : Fin rows.length)
    (column : Nat) (value : Rat) (selected : rows[row.val][column]?=some value) :
    ∃ time ≤ 4000*((Encoding.rationalMatrix.encode rows).length+row.val+column+3),
      Executes inspect (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true)
        (List.replicate (column+1) true) [] [] [] [] []) time
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true)
          (List.replicate (column+1) true) (Encoding.rationalRow.encode rows[row.val])
          (Encoding.rational.encode value) [true] [true] [decide (value=0)]) := by
  obtain ⟨readTime,readBound,readRun⟩ := readRow_executes rows row (List.replicate (column+1) true)
  obtain ⟨inspectTime,inspectBound,inspected⟩ := inspectRow_executes (Encoding.rationalMatrix.encode rows)
    (List.replicate (row.val+1) true) rows[row.val] column value selected
  have size := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[row.val] (List.getElem_mem row.isLt)
  change (Encoding.rationalRow.encode rows[row.val]).length ≤ (Encoding.rationalMatrix.encode rows).length at size
  exact ⟨_,by omega,readRun.sequence inspected⟩

end Counting.StackMachine.GaussianEntry
