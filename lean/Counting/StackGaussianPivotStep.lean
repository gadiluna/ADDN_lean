import Counting.StackGaussianEntry
import Counting.StackReadBranch

namespace Counting.StackMachine.GaussianPivot
open Routine

def file (matrix rowIndex columnIndex row coefficient rowPresent coefficientPresent zero counter active : List Bool) : Fin 31 → List Bool :=
  ![matrix,rowIndex,columnIndex,row,coefficient,rowPresent,coefficientPresent,zero,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],counter,active]

def state (matrix : List Bool) (row column : Nat) (counter : List Bool) (active : Bool) : Fin 31 → List Bool :=
  file matrix (List.replicate (row+1) true) (List.replicate (column+1) true)
    [] [] [] [] [] counter [active]

def entryRoles : Fin 29 ↪ Fin 31 := ⟨fun r => ⟨r.val,by omega⟩,by intro a b equal; exact Fin.ext (congrArg (fun r : Fin 31 => r.val) equal)⟩
abbrev inspect : Routine 29 := relocate GaussianEntry.inspect entryRoles
abbrev clean : Routine 29 := clearRegisters [3,4,5,6,7]
abbrev stop : Routine 29 := sequence (clear 30) (pushBit 30 false)
abbrev afterZero : Routine 29 := sequence clean (pushBit 1 true)
abbrev afterNonzero : Routine 29 := sequence clean stop
abbrev activeStep : Routine 29 := sequence inspect (branchRead 7 afterZero afterNonzero)
abbrev body : Routine 29 := branchRead 30 activeStep (skip 29)

theorem inspect_executes (rows : List (List Rat)) (row : Fin rows.length)
    (column : Nat) (value : Rat) (selected : rows[row.val][column]?=some value)
    (counter : List Bool) :
    ∃ time ≤ 4000*((Encoding.rationalMatrix.encode rows).length+row.val+column+3),
      Executes inspect (state (Encoding.rationalMatrix.encode rows) row.val column counter true) time
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (row.val+1) true)
          (List.replicate (column+1) true) (Encoding.rationalRow.encode rows[row.val])
          (Encoding.rational.encode value) [true] [true] [decide (value=0)] counter [true]) := by
  obtain ⟨time,bounded,ran⟩ := GaussianEntry.inspect_executes rows row column value selected
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame GaussianEntry.inspect entryRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [state,file,GaussianEntry.file,entryRoles]
  · intro r; fin_cases r <;> simp [file,GaussianEntry.file,entryRoles]
  · intro r outside
    have lower : 29≤r.val := by
      by_contra bounded
      have small : r.val<29 := by omega
      exact outside ⟨r.val,small⟩ (Fin.ext rfl)
    fin_cases r <;> simp_all [state,file]

theorem clean_executes (matrix rowIndex columnIndex row coefficient counter : List Bool)
    (zero active : Bool) (bound : Nat)
    (hm : matrix.length≤bound) (hi : rowIndex.length≤bound) (hj : columnIndex.length≤bound)
    (hr : row.length≤bound) (hc : coefficient.length≤bound) (ht : counter.length≤bound)
    (positive : 1≤bound) :
    ∃ time ≤ 5*(bound+2),
      Executes clean (file matrix rowIndex columnIndex row coefficient [true] [true] [zero] counter [active]) time
        (file matrix rowIndex columnIndex [] [] [] [] [] counter [active]) := by
  obtain ⟨time,bounded,ran⟩ := clearRegisters_executes ([3,4,5,6,7] : List (Fin 31))
    (file matrix rowIndex columnIndex row coefficient [true] [true] [zero] counter [active]) bound
    (by intro r; fin_cases r <;> simp [file] <;> assumption)
  refine ⟨time,by simpa using bounded,?_⟩
  convert ran using 1
  funext r; fin_cases r <;> simp [clearedStore,file]

theorem stop_executes (matrix : List Bool) (row column : Nat) (counter : List Bool) :
    Executes stop (state matrix row column counter true) 4 (state matrix row column counter false) := by
  have ran := (clear_executes (30 : Fin 31) (state matrix row column counter true)).sequence
    (pushBit_executes 30 false (Function.update (state matrix row column counter true) 30 []))
  convert ran using 1
  · rfl
  · funext r; fin_cases r <;> simp [state,file]

theorem activeStep_executes (rows : List (List Rat)) (row : Fin rows.length)
    (column : Nat) (value : Rat) (selected : rows[row.val][column]?=some value)
    (counter : List Bool) :
    ∃ time ≤ 5000*((Encoding.rationalMatrix.encode rows).length+row.val+column+counter.length+6),
      Executes activeStep (state (Encoding.rationalMatrix.encode rows) row.val column counter true) time
        (if value=0 then state (Encoding.rationalMatrix.encode rows) (row.val+1) column counter true
         else state (Encoding.rationalMatrix.encode rows) row.val column counter false) := by
  let matrix := Encoding.rationalMatrix.encode rows
  let bound := matrix.length+row.val+column+counter.length+2
  obtain ⟨inspectTime,inspectBound,inspected⟩ := inspect_executes rows row column value selected counter
  have rowSize := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[row.val] (List.getElem_mem row.isLt)
  change (Encoding.rationalRow.encode rows[row.val]).length≤matrix.length at rowSize
  have coefficientSize := RowScale.member_row_length_le rows[row.val] value (List.mem_of_getElem? selected)
  obtain ⟨cleanTime,cleanBound,cleaned⟩ := clean_executes matrix
    (List.replicate (row.val+1) true) (List.replicate (column+1) true)
    (Encoding.rationalRow.encode rows[row.val]) (Encoding.rational.encode value) counter (decide (value=0)) true bound
    (by dsimp [bound];omega) (by simp [bound];omega) (by simp [bound];omega)
    (by dsimp [bound];omega) (by dsimp [bound];omega) (by dsimp [bound];omega) (by dsimp [bound];omega)
  let before := file matrix (List.replicate (row.val+1) true) (List.replicate (column+1) true)
    (Encoding.rationalRow.encode rows[row.val]) (Encoding.rational.encode value) [true] [true]
    [decide (value=0)] counter [true]
  by_cases isZero : value=0
  · have pushed := pushBit_executes (1 : Fin 31) true (state matrix row.val column counter true)
    have result : Function.update (state matrix row.val column counter true) 1
        (true::state matrix row.val column counter true 1)=state matrix (row.val+1) column counter true := by
      funext r; fin_cases r <;> simp [state,file,List.replicate_succ]
    rw [result] at pushed
    have next := cleaned.sequence pushed
    have chosen : Executes (if decide (value=0) then afterZero else afterNonzero)
        before (cleanTime+1+1) (state matrix (row.val+1) column counter true) := by
      simpa [before,isZero] using next
    have branch := branchRead_executes (7 : Fin 31) afterZero afterNonzero (decide (value=0)) []
      before _ _ rfl chosen
    refine ⟨inspectTime+1+(cleanTime+1+1+3),?_,?_⟩
    · dsimp [bound,matrix] at cleanBound
      omega
    · simpa only [if_pos isZero] using inspected.sequence branch
  · have next := cleaned.sequence (stop_executes matrix row.val column counter)
    have chosen : Executes (if decide (value=0) then afterZero else afterNonzero)
        before (cleanTime+1+4) (state matrix row.val column counter false) := by
      simpa [before,isZero] using next
    have branch := branchRead_executes (7 : Fin 31) afterZero afterNonzero (decide (value=0)) []
      before _ _ rfl chosen
    refine ⟨inspectTime+1+(cleanTime+1+4+3),?_,?_⟩
    · dsimp [bound,matrix] at cleanBound
      omega
    · simpa only [if_neg isZero] using inspected.sequence branch

theorem body_inactive (matrix : List Bool) (row column : Nat) (counter : List Bool) :
    Executes body (state matrix row column counter false) 3 (state matrix row column counter false) := by
  exact branchRead_executes 30 activeStep (skip 29) false [] _ _ 0 rfl (skip_executes _)

theorem body_active (rows : List (List Rat)) (row : Fin rows.length)
    (column : Nat) (value : Rat) (selected : rows[row.val][column]?=some value)
    (counter : List Bool) :
    ∃ time ≤ 5000*((Encoding.rationalMatrix.encode rows).length+row.val+column+counter.length+7),
      Executes body (state (Encoding.rationalMatrix.encode rows) row.val column counter true) time
        (if value=0 then state (Encoding.rationalMatrix.encode rows) (row.val+1) column counter true
         else state (Encoding.rationalMatrix.encode rows) row.val column counter false) := by
  obtain ⟨time,bounded,ran⟩ := activeStep_executes rows row column value selected counter
  exact ⟨time+3,by omega,branchRead_executes 30 activeStep (skip 29) true [] _ _ time rfl ran⟩

end Counting.StackMachine.GaussianPivot
