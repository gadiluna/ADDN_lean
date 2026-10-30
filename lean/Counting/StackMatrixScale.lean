import Counting.StackRowScaleBounds
import Counting.StackMatrixSwapBounds

namespace Counting.StackMachine.MatrixScale
open Routine FieldAccess
set_option backward.isDefEq.respectTransparency false

/-- The row program occupies registers 0..31. Matrix, bounded unary index,
and reader flag are outside that workspace. -/
def file (factor matrix index input output flag : List Bool) : Fin 35 → List Bool :=
  fun r => if small : r.val<32 then
    RowScale.file factor input output [] [] [] [] [] [] ⟨r.val,small⟩
  else if r=32 then matrix else if r=33 then index else flag

def rowRoles : Fin 32 ↪ Fin 35 := ⟨fun r => r.castLE (by decide),by
  intro a b equal
  exact Fin.ext (congrArg (fun r : Fin 35 => r.val) equal)⟩
def readRoles : Fin 8 ↪ Fin 35 := ⟨![32,33,1,34,3,4,5,6],by decide⟩
def writeRoles : Fin 6 ↪ Fin 35 := ⟨![32,33,2,3,4,5],by decide⟩

abbrev readRow : Routine 33 := preservingRead 27 readRoles
abbrev scaleRow : Routine 33 := relocate RowScale.scaleRoutine rowRoles
abbrev writeRow : Routine 33 := writePayload 29 writeRoles
abbrev scaleRoutine : Routine 33 := sequence readRow
  (sequence scaleRow (sequence writeRow (clear 34)))

theorem readRow_executes (factor : List Bool) (rows : List (List Rat)) (index : Fin rows.length) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(index.val+1)+14,
      Executes readRow
        (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) [] [] []) time
        (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true)
          (Encoding.rationalRow.encode rows[index.val]) [] [true]) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 27 readRoles
    (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) [] [] [])
    rows index.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,readRoles,RowScale.file,index.isLt]

theorem scaleRow_executes (factor : Rat) (row : List Rat) (matrix index flag : List Bool) :
    ∃ time ≤ 300000000*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode row).length+1)^4,
      Executes scaleRow (file (Encoding.rational.encode factor) matrix index (Encoding.rationalRow.encode row) [] flag)
        time (file (Encoding.rational.encode factor) matrix index [] (Encoding.rationalRow.encode (row.map (factor*·))) flag) := by
  obtain ⟨time,bounded,ran⟩ := RowScale.scale_executes_polynomial factor row []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at bounded ran
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RowScale.scaleRoutine rowRoles _ _ _ _ time _ _ _ ran
  · funext r
    simp [file,rowRoles,r.isLt]
  · intro r
    simp [file,rowRoles,r.isLt]
  · intro r outside
    have large : ¬r.val<32 := by
      intro small
      exact outside ⟨r.val,small⟩ (by apply Fin.ext;rfl)
    simp only [file,dif_neg large]

theorem writeRow_executes (factor : List Bool) (rows : List (List Rat))
    (index : Fin rows.length) (replacement : List Rat) :
    ∃ time ≤ 5*(Encoding.rationalMatrix.encode rows).length+3*(index.val+1)+
        17*(Encoding.rationalRow.encode replacement).length+21,
      Executes writeRow
        (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true)
          [] (Encoding.rationalRow.encode replacement) [true]) time
        (file factor (Encoding.rationalMatrix.encode (rows.set index.val replacement)) [] [] [] [true]) := by
  obtain ⟨time,bounded,ran⟩ := writePayload_framedList_executes Encoding.rationalRow 29 writeRoles
    (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true)
      [] (Encoding.rationalRow.encode replacement) [true])
    rows index.val replacement index.isLt rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,writeRoles,RowScale.file,Encoding.rationalMatrix]

theorem scale_executes (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    ∃ time ≤ 15*(Encoding.rationalMatrix.encode rows).length+11*(index.val+1)+
      300000000*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode rows[index.val]).length+1)^4+
      17*(Encoding.rationalRow.encode (rows[index.val].map (factor*·))).length+40,
      Executes scaleRoutine
        (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
          (List.replicate (index.val+1) true) [] [] []) time
        (file (Encoding.rational.encode factor)
          (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))) [] [] [] []) := by
  obtain ⟨a,ha,ra⟩ := readRow_executes (Encoding.rational.encode factor) rows index
  obtain ⟨b,hb,rb⟩ := scaleRow_executes factor rows[index.val] (Encoding.rationalMatrix.encode rows)
    (List.replicate (index.val+1) true) [true]
  obtain ⟨c,hc,rc⟩ := writeRow_executes (Encoding.rational.encode factor) rows index (rows[index.val].map (factor*·))
  have cleaned := clear_executes (registers := 33) 34
    (file (Encoding.rational.encode factor)
      (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))) [] [] [] [true])
  change Executes _ _ 2 _ at cleaned
  have cleared : Function.update
      (file (Encoding.rational.encode factor)
        (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))) [] [] [] [true]) 34 [] =
      file (Encoding.rational.encode factor)
        (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))) [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowScale.file]
  rw [cleared] at cleaned
  exact ⟨_,by omega,ra.sequence (rb.sequence (rc.sequence cleaned))⟩

end Counting.StackMachine.MatrixScale
