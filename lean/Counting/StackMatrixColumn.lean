import Counting.StackGaussianRhsBounds

namespace Counting.StackMachine.MatrixColumn
open Routine
set_option backward.isDefEq.respectTransparency false

def file (source output localIndex localCount matrix index count : List Bool) : Fin 16 → List Bool :=
  ![source,output,[],[],localIndex,[],[],[],[],[],localCount,[],[],matrix,index,count]
def roles : Fin 13 ↪ Fin 16 := ⟨fun r => ⟨r.val,by omega⟩,
  by intro a b equal;apply Fin.ext;exact congrArg (fun r : Fin 16 => r.val) equal⟩
abbrev copyInputs : Routine 14 := sequence (ofProgram (ListPrograms.copyProgram 13 13 0 6))
  (sequence (ofProgram (ListPrograms.copyProgram 13 14 4 6)) (ofProgram (ListPrograms.copyProgram 13 15 10 6)))
abbrev readColumn : Routine 14 := sequence copyInputs
  (sequence (relocate GaussianRhs.extract roles) (clear 4))

theorem column_length_le (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) :
    (Encoding.rationalRow.encode values).length ≤ (Encoding.rationalMatrix.encode rows).length := by
  have fields := GaussianRhs.selected_sequence_length rows values column selected
  change (Encoding.natural.encode values.length++_).length ≤ (Encoding.natural.encode rows.length++_).length
  rw [← selected.length_eq]
  simp only [List.length_append]
  omega

theorem copyInputs_executes (matrix index count : List Bool) :
    Executes copyInputs (file [] [] [] [] matrix index count)
      (5*matrix.length+5*index.length+5*count.length+8)
      (file matrix [] index count matrix index count) := by
  have matrixRun := copy_executes 13 (13 : Fin 16) 0 6 (by decide) (by decide) (by decide) (file [] [] [] [] matrix index count) rfl
  have matrixStore : Function.update (file [] [] [] [] matrix index count) 0 (matrix++[])=(file matrix [] [] [] matrix index count) := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*matrix.length+2) (Function.update (file [] [] [] [] matrix index count) 0 (matrix++[])) at matrixRun
  rw [matrixStore] at matrixRun
  have indexRun := copy_executes 13 (14 : Fin 16) 4 6 (by decide) (by decide) (by decide) (file matrix [] [] [] matrix index count) rfl
  have indexStore : Function.update (file matrix [] [] [] matrix index count) 4 (index++[])=(file matrix [] index [] matrix index count) := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*index.length+2) (Function.update (file matrix [] [] [] matrix index count) 4 (index++[])) at indexRun
  rw [indexStore] at indexRun
  have countRun := copy_executes 13 (15 : Fin 16) 10 6 (by decide) (by decide) (by decide) (file matrix [] index [] matrix index count) rfl
  have countStore : Function.update (file matrix [] index [] matrix index count) 10 (count++[])=(file matrix [] index count matrix index count) := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*count.length+2) (Function.update (file matrix [] index [] matrix index count) 10 (count++[])) at countRun
  rw [countStore] at countRun
  convert matrixRun.sequence (indexRun.sequence countRun) using 1
  omega

/-- Matrix, unary index, and unary row count are preserved. A copied matrix
is traversed to produce the requested canonical column, and private buffers
are emptied. The count is an explicit input, not an uncharged conversion. -/
theorem readColumn_executes (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) :
    ∃ time ≤ 2020*((Encoding.rationalMatrix.encode rows).length+column+2)^2,
      Executes readColumn
        (file [] [] [] [] (Encoding.rationalMatrix.encode rows)
          (List.replicate (column+1) true) (List.replicate rows.length true)) time
        (file [] (Encoding.rationalRow.encode values) [] [] (Encoding.rationalMatrix.encode rows)
          (List.replicate (column+1) true) (List.replicate rows.length true)) := by
  let matrix := Encoding.rationalMatrix.encode rows
  let index := List.replicate (column+1) true
  let count := List.replicate rows.length true
  have copied := copyInputs_executes matrix index count
  obtain ⟨extractTime,extractBound,extracted⟩ := GaussianRhs.extract_executes_polynomial rows values column selected
  have called : Executes (relocate GaussianRhs.extract roles)
      (file matrix [] index count matrix index count) extractTime
      (file [] (Encoding.rationalRow.encode values) index [] matrix index count) := by
    apply relocate_executes_frame GaussianRhs.extract roles _ _ _ _ extractTime _ _ _ extracted
    · funext r;fin_cases r <;> simp [file,roles,GaussianRhs.state,GaussianRhs.file,index,count,matrix]
    · intro r;fin_cases r <;> simp [file,roles,GaussianRhs.state,GaussianRhs.file,index,count,matrix]
    · intro r outside
      fin_cases r
      all_goals first | exact False.elim (outside 0 rfl) | exact False.elim (outside 1 rfl) |
        exact False.elim (outside 10 rfl) | simp [file]
  have cleared := clear_executes (4 : Fin 16)
    (file [] (Encoding.rationalRow.encode values) index [] matrix index count)
  have clearedStore : Function.update (file [] (Encoding.rationalRow.encode values) index [] matrix index count) 4 [] =
      file [] (Encoding.rationalRow.encode values) [] [] matrix index count := by
    funext r;fin_cases r <;> simp [file]
  change Executes (clear 4) _ (index.length+1)
    (Function.update (file [] (Encoding.rationalRow.encode values) index [] matrix index count) 4 []) at cleared
  rw [clearedStore] at cleared
  refine ⟨_,?_,copied.sequence (called.sequence cleared)⟩
  have countBound := Encoding.framedList_count_le Encoding.rationalRow rows
  change rows.length ≤ matrix.length at countBound
  change extractTime ≤ 2000*(matrix.length+column+2)^2 at extractBound
  simp only [index,count,List.length_replicate]
  have linear : matrix.length+column+2 ≤ (matrix.length+column+2)^2 := by nlinarith
  change _≤2020*(matrix.length+column+2)^2
  omega

end Counting.StackMachine.MatrixColumn
