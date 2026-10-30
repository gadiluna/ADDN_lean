import Counting.StackFramedWrite

namespace Counting.StackMachine.MatrixSwap
open Routine FieldAccess

def file (matrix first second left right flag : List Bool) : Fin 10 → List Bool :=
  ![matrix,first,second,left,right,flag,[],[],[],[]]

def firstReadRoles : Fin 8 ↪ Fin 10 := ⟨![0,1,3,5,6,7,8,9],by decide⟩
def secondReadRoles : Fin 8 ↪ Fin 10 := ⟨![0,2,4,5,6,7,8,9],by decide⟩
def firstWriteRoles : Fin 6 ↪ Fin 10 := ⟨![0,1,4,6,7,8],by decide⟩
def secondWriteRoles : Fin 6 ↪ Fin 10 := ⟨![0,2,3,6,7,8],by decide⟩

abbrev firstRead : Routine 8 := preservingRead 2 firstReadRoles
abbrev secondRead : Routine 8 := preservingRead 2 secondReadRoles
abbrev firstWrite : Routine 8 := writePayload 4 firstWriteRoles
abbrev secondWrite : Routine 8 := writePayload 4 secondWriteRoles

/-- Both old rows are read before either replacement, so coincident indices
also produce the intended unchanged matrix. All row payloads stay serialized. -/
abbrev swapRoutine : Routine 8 := sequence firstRead (sequence secondRead
  (sequence firstWrite (sequence secondWrite (clear 5))))

theorem firstRead_executes (rows : List (List Rat)) (index : Fin rows.length) (other : List Bool) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(index.val+1)+14,
      Executes firstRead
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) other [] [] []) time
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) other
          (Encoding.rationalRow.encode rows[index.val]) [] [true]) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 2 firstReadRoles
    (file (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) other [] [] [])
    rows index.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,firstReadRoles,index.isLt]

theorem secondRead_executes (rows : List (List Rat)) (index : Fin rows.length)
    (other left : List Bool) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(index.val+1)+14,
      Executes secondRead
        (file (Encoding.rationalMatrix.encode rows) other (List.replicate (index.val+1) true) left [] [true]) time
        (file (Encoding.rationalMatrix.encode rows) other (List.replicate (index.val+1) true) left
          (Encoding.rationalRow.encode rows[index.val]) [true,true]) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 2 secondReadRoles
    (file (Encoding.rationalMatrix.encode rows) other (List.replicate (index.val+1) true) left [] [true])
    rows index.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,secondReadRoles,index.isLt]

theorem firstWrite_executes (rows : List (List Rat)) (index : Fin rows.length)
    (replacement : List Rat) (other left : List Bool) :
    ∃ time ≤ 5*(Encoding.rationalMatrix.encode rows).length+3*(index.val+1)+
        17*(Encoding.rationalRow.encode replacement).length+21,
      Executes firstWrite
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) other left
          (Encoding.rationalRow.encode replacement) [true,true]) time
        (file (Encoding.rationalMatrix.encode (rows.set index.val replacement)) [] other left [] [true,true]) := by
  obtain ⟨time,bounded,ran⟩ := writePayload_framedList_executes Encoding.rationalRow 4 firstWriteRoles
    (file (Encoding.rationalMatrix.encode rows) (List.replicate (index.val+1) true) other left
      (Encoding.rationalRow.encode replacement) [true,true])
    rows index.val replacement index.isLt rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,firstWriteRoles,Encoding.rationalMatrix]

theorem secondWrite_executes (rows : List (List Rat)) (index : Fin rows.length)
    (replacement : List Rat) :
    ∃ time ≤ 5*(Encoding.rationalMatrix.encode rows).length+3*(index.val+1)+
        17*(Encoding.rationalRow.encode replacement).length+21,
      Executes secondWrite
        (file (Encoding.rationalMatrix.encode rows) [] (List.replicate (index.val+1) true)
          (Encoding.rationalRow.encode replacement) [] [true,true]) time
        (file (Encoding.rationalMatrix.encode (rows.set index.val replacement)) [] [] [] [] [true,true]) := by
  obtain ⟨time,bounded,ran⟩ := writePayload_framedList_executes Encoding.rationalRow 4 secondWriteRoles
    (file (Encoding.rationalMatrix.encode rows) [] (List.replicate (index.val+1) true)
      (Encoding.rationalRow.encode replacement) [] [true,true])
    rows index.val replacement index.isLt rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [file,secondWriteRoles,Encoding.rationalMatrix]

theorem swap_executes (rows : List (List Rat)) (first second : Fin rows.length) :
    ∃ time ≤ 25*(Encoding.rationalMatrix.encode rows).length+
        5*(Encoding.rationalMatrix.encode (rows.set first.val rows[second.val])).length+
        11*(first.val+second.val+2)+17*((Encoding.rationalRow.encode rows[first.val]).length+
          (Encoding.rationalRow.encode rows[second.val]).length)+77,
      Executes swapRoutine
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (first.val+1) true)
          (List.replicate (second.val+1) true) [] [] []) time
        (file (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
          [] [] [] [] []) := by
  obtain ⟨a,ha,ra⟩ := firstRead_executes rows first (List.replicate (second.val+1) true)
  obtain ⟨b,hb,rb⟩ := secondRead_executes rows second (List.replicate (first.val+1) true)
    (Encoding.rationalRow.encode rows[first.val])
  obtain ⟨c,hc,rc⟩ := firstWrite_executes rows first rows[second.val] (List.replicate (second.val+1) true)
    (Encoding.rationalRow.encode rows[first.val])
  obtain ⟨d,hd,rd⟩ := secondWrite_executes (rows.set first.val rows[second.val])
    ⟨second.val,by simp [second.isLt]⟩ rows[first.val]
  have cleaned : Executes (clear (registers := 8) 5)
      (file (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
        [] [] [] [] [true,true]) 3
      (file (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
        [] [] [] [] []) := by
    have run := clear_executes (registers := 8) 5
      (file (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
        [] [] [] [] [true,true])
    change Executes _ _ 3 _ at run
    convert run using 1
    funext r; fin_cases r <;> simp [file]
  refine ⟨_,?_,ra.sequence (rb.sequence (rc.sequence (rd.sequence cleaned)))⟩
  dsimp only at hd
  omega

end Counting.StackMachine.MatrixSwap
