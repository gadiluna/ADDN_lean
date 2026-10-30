import Counting.StackFramedList
import Counting.StackUnframeCanonical
import Counting.StackEncodingFrameStore
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.GaussianRhs
open Routine EncodingPrograms FieldAccess
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def file (source output row value index flag counter header temporary : List Bool) : Fin 13 → List Bool :=
  ![source,output,row,value,index,flag,[],[],[],[],counter,header,temporary]

def state (source output : List Bool) (column : Nat) (counter header : List Bool) : Fin 13 → List Bool :=
  file source output [] [] (List.replicate (column+1) true) [] counter header []

def readerRoles : Fin 8 ↪ Fin 13 := ⟨![2,4,3,5,6,7,8,9],by decide⟩
abbrev readRow : Routine 11 := ofProgram (unframeProgram 10 0 2 6)
abbrev readValue : Routine 11 := preservingRead 5 readerRoles
abbrev discard : Routine 11 := sequence (clear 2) (clear 5)
abbrev emitValue : Routine 11 := sequence (frameRoutine 10 3 12 6)
  (ofProgram (ListPrograms.reverseProgram 11 12 1))
abbrev body : Routine 11 := sequence readRow (sequence readValue (sequence discard emitValue))

theorem readRow_executes (row : List Rat) (suffix output : List Bool) (column : Nat) (counter header : List Bool) :
    Executes readRow
      (state (Encoding.frame (Encoding.rationalRow.encode row)++suffix) output column counter header)
      (5*(Encoding.rationalRow.encode row).length+2)
      (file suffix output (Encoding.rationalRow.encode row) [] (List.replicate (column+1) true) [] counter header []) := by
  have ran := unframe_canonical_executes 10 (0 : Fin 13) 2 6 (by decide) (by decide) (by decide)
    (state (Encoding.frame (Encoding.rationalRow.encode row)++suffix) output column counter header)
    (Encoding.rationalRow.encode row) suffix rfl rfl
  convert ran using 1
  · rfl
  · funext r;fin_cases r <;> simp [state,file]

theorem readValue_executes (row : List Rat) (value : Rat) (column : Nat) (selected : row[column]?=some value)
    (suffix output counter header : List Bool) :
    ∃ time ≤ 10*(Encoding.rationalRow.encode row).length+8*(column+1)+14,
      Executes readValue
        (file suffix output (Encoding.rationalRow.encode row) [] (List.replicate (column+1) true) [] counter header []) time
        (file suffix output (Encoding.rationalRow.encode row) (Encoding.rational.encode value)
          (List.replicate (column+1) true) [true] counter header []) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rational 5 readerRoles
    (file suffix output (Encoding.rationalRow.encode row) [] (List.replicate (column+1) true) [] counter header [])
    row column rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r;fin_cases r <;> simp [file,readerRoles,selected]

theorem discard_executes (source output row value index counter header : List Bool) :
    Executes discard (file source output row value index [true] counter header []) (row.length+4)
      (file source output [] value index [] counter header []) := by
  have a := clear_executes (2 : Fin 13) (file source output row value index [true] counter header [])
  have middle : Function.update (file source output row value index [true] counter header []) 2 []=
      file source output [] value index [true] counter header [] := by
    funext r;fin_cases r <;> simp [file]
  rw [middle] at a
  have b := clear_executes (5 : Fin 13) (file source output [] value index [true] counter header [])
  have final : Function.update (file source output [] value index [true] counter header []) 5 []=
      file source output [] value index [] counter header [] := by
    funext r;fin_cases r <;> simp [file]
  rw [final] at b
  exact a.sequence b

theorem emitValue_executes (source output value index counter header : List Bool) :
    Executes emitValue (file source output [] value index [] counter header [])
      (9*value.length+8)
      (file source ((Encoding.frame value).reverse++output) [] [] index [] counter header []) := by
  have a := frame_executes_updates 10 (3 : Fin 13) 12 6 (by decide) (by decide) (by decide)
    (file source output [] value index [] counter header []) rfl
  have middle : Function.update (Function.update (file source output [] value index [] counter header []) 3 [])
      12 (Encoding.frame value++[]) = file source output [] [] index [] counter header (Encoding.frame value) := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*value.length+4)
    (Function.update (Function.update (file source output [] value index [] counter header []) 3 [])
      12 (Encoding.frame value++[])) at a
  rw [middle] at a
  have b := reverse_executes 11 (12 : Fin 13) 1 (by decide)
    (file source output [] [] index [] counter header (Encoding.frame value))
  have final : Function.update (Function.update (file source output [] [] index [] counter header (Encoding.frame value)) 12 [])
      1 ((Encoding.frame value).reverse++output)=file source ((Encoding.frame value).reverse++output) [] [] index [] counter header [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (2*(Encoding.frame value).length+1)
    (Function.update (Function.update (file source output [] [] index [] counter header (Encoding.frame value)) 12 [])
      1 ((Encoding.frame value).reverse++output)) at b
  rw [final,Encoding.frame_length] at b
  convert a.sequence b using 1
  omega

/-- Extract one selected rational field and append it in output order using
an explicitly reversed accumulator. The row buffer and all scratch fields
are erased by the executed code. -/
theorem body_executes (row : List Rat) (value : Rat) (column : Nat) (selected : row[column]?=some value)
    (suffix output counter header : List Bool) :
    ∃ time ≤ 100*((Encoding.rationalRow.encode row).length+column+2),
      Executes body (state (Encoding.frame (Encoding.rationalRow.encode row)++suffix) output column counter header) time
        (state suffix ((Encoding.frame (Encoding.rational.encode value)).reverse++output) column counter header) := by
  have a := readRow_executes row suffix output column counter header
  obtain ⟨readTime,readBound,b⟩ := readValue_executes row value column selected suffix output counter header
  have c := discard_executes suffix output (Encoding.rationalRow.encode row) (Encoding.rational.encode value)
    (List.replicate (column+1) true) counter header
  have d := emitValue_executes suffix output (Encoding.rational.encode value) (List.replicate (column+1) true) counter header
  have member := List.mem_of_getElem? selected
  have valueBound := RowScale.member_row_length_le row value member
  exact ⟨_,by omega,a.sequence (b.sequence (c.sequence d))⟩

end Counting.StackMachine.GaussianRhs
