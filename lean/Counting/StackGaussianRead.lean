import Counting.StackGaussianBank

namespace Counting.StackMachine.GaussianBank
open Routine
set_option backward.isDefEq.respectTransparency false

def entryRoles : Fin 29 ↪ Fin 52 := ⟨![37,38,39,1,0,40,41,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],by decide⟩

def inspected (matrix first second row coefficient rowFlag coefficientFlag zero : List Bool)
    (saved : Fin 10 → List Bool) : Fin 52 → List Bool :=
  bank (MatrixAxpy.file coefficient matrix first second row zero [] rowFlag coefficientFlag) saved

abbrev inspect : Routine 50 := relocate GaussianEntry.inspect entryRoles
abbrev cleanEntry : Routine 50 := sequence (clear 1) (sequence (clear 2) (sequence (clear 40) (clear 41)))
abbrev readCoefficient : Routine 50 := sequence inspect cleanEntry

theorem inspect_executes (rows : List (List Rat)) (row : Fin rows.length) (column : Nat) (value : Rat)
    (selected : rows[row.val][column]?=some value) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 4000*((Encoding.rationalMatrix.encode rows).length+row.val+column+3),
      Executes inspect
        (ready (Encoding.rationalMatrix.encode rows) [] (List.replicate (row.val+1) true)
          (List.replicate (column+1) true) saved) time
        (inspected (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true)
          (List.replicate (column+1) true) (Encoding.rationalRow.encode rows[row.val])
          (Encoding.rational.encode value) [true] [true] [decide (value=0)] saved) := by
  obtain ⟨time,bounded,ran⟩ := GaussianEntry.inspect_executes rows row column value selected
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianEntry.inspect entryRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [ready,bank,entryRoles,MatrixAxpy.file,RowAxpy.file,GaussianEntry.file]
  · intro r;fin_cases r <;> simp [inspected,bank,entryRoles,MatrixAxpy.file,RowAxpy.file,GaussianEntry.file]
  · intro r outside
    have factor := outside 4
    have target := outside 3
    have zero := outside 7
    have rowFlag := outside 5
    have coefficientFlag := outside 6
    fin_cases r <;> simp_all [inspected,ready,bank,entryRoles,MatrixAxpy.file,RowAxpy.file]

theorem cleanEntry_executes (matrix first second row coefficient : List Bool) (zero : Bool)
    (saved : Fin 10 → List Bool) :
    Executes cleanEntry (inspected matrix first second row coefficient [true] [true] [zero] saved)
      (row.length+10) (ready matrix coefficient first second saved) := by
  let initial := inspected matrix first second row coefficient [true] [true] [zero] saved
  let a := inspected matrix first second [] coefficient [true] [true] [zero] saved
  let b := inspected matrix first second [] coefficient [true] [true] [] saved
  let c := inspected matrix first second [] coefficient [] [true] [] saved
  have firstRun := clear_executes (1 : Fin 52) initial
  have firstStore : Function.update initial 1 []=a := by
    funext r;fin_cases r <;> simp [initial,a,inspected,bank,MatrixAxpy.file,RowAxpy.file]
  rw [firstStore] at firstRun
  have secondRun := clear_executes (2 : Fin 52) a
  have secondStore : Function.update a 2 []=b := by
    funext r;fin_cases r <;> simp [a,b,inspected,bank,MatrixAxpy.file,RowAxpy.file]
  rw [secondStore] at secondRun
  have thirdRun := clear_executes (40 : Fin 52) b
  have thirdStore : Function.update b 40 []=c := by
    funext r;fin_cases r <;> simp [b,c,inspected,bank,MatrixAxpy.file,RowAxpy.file]
  rw [thirdStore] at thirdRun
  have fourthRun := clear_executes (41 : Fin 52) c
  have fourthStore : Function.update c 41 []=ready matrix coefficient first second saved := by
    funext r;fin_cases r <;> simp [c,inspected,ready,bank,MatrixAxpy.file,RowAxpy.file]
  rw [fourthStore] at fourthRun
  change Executes _ initial (row.length+1) a at firstRun
  change Executes _ a 2 b at secondRun
  change Executes _ b 2 c at thirdRun
  change Executes _ c 2 _ at fourthRun
  convert firstRun.sequence (secondRun.sequence (thirdRun.sequence fourthRun)) using 1

/-- A physical indexed read of a rational coefficient. The full serialized
row is erased after the read; both charged unary indices are retained. -/
theorem readCoefficient_executes (rows : List (List Rat)) (row : Fin rows.length) (column : Nat) (value : Rat)
    (selected : rows[row.val][column]?=some value) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 5000*((Encoding.rationalMatrix.encode rows).length+row.val+column+3),
      Executes readCoefficient
        (ready (Encoding.rationalMatrix.encode rows) [] (List.replicate (row.val+1) true)
          (List.replicate (column+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode rows) (Encoding.rational.encode value)
          (List.replicate (row.val+1) true) (List.replicate (column+1) true) saved) := by
  obtain ⟨time,bounded,ran⟩ := inspect_executes rows row column value selected saved
  have cleaned := cleanEntry_executes (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true)
    (List.replicate (column+1) true) (Encoding.rationalRow.encode rows[row.val]) (Encoding.rational.encode value)
    (decide (value=0)) saved
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[row.val] (List.getElem_mem row.isLt)
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at rowBound
  exact ⟨_,by omega,ran.sequence cleaned⟩

end Counting.StackMachine.GaussianBank
