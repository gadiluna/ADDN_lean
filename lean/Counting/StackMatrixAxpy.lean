import Counting.StackRowAxpyBounds
import Counting.StackMatrixSwapBounds

namespace Counting.StackMachine.MatrixAxpy
open Routine FieldAccess
set_option backward.isDefEq.respectTransparency false

/-- The complete row workspace precedes the matrix, both unary indices,
and independent reader flags. Both original rows are fetched before writing. -/
def file (factor matrix targetIndex sourceIndex target source result targetFlag sourceFlag : List Bool) : Fin 42 → List Bool :=
  fun r => if small : r.val<37 then RowAxpy.file factor target source result ⟨r.val,small⟩
    else if r=37 then matrix else if r=38 then targetIndex else if r=39 then sourceIndex
    else if r=40 then targetFlag else sourceFlag

def rowRoles : Fin 37 ↪ Fin 42 := ⟨fun r=>r.castLE (by decide),by
  intro a b equal; exact Fin.ext (congrArg (fun r : Fin 42=>r.val) equal)⟩
def targetRoles : Fin 8 ↪ Fin 42 := ⟨![37,38,1,40,4,5,6,7],by decide⟩
def sourceRoles : Fin 8 ↪ Fin 42 := ⟨![37,39,2,41,4,5,6,7],by decide⟩
def writeRoles : Fin 6 ↪ Fin 42 := ⟨![37,38,3,4,5,6],by decide⟩

abbrev readTarget : Routine 40 := preservingRead 34 targetRoles
abbrev readSource : Routine 40 := preservingRead 34 sourceRoles
abbrev axpyRows : Routine 40 := relocate RowAxpy.axpyRoutine rowRoles
abbrev writeRow : Routine 40 := writePayload 36 writeRoles
abbrev cleanup : Routine 40 := sequence (clear 39) (sequence (clear 40) (clear 41))
abbrev axpyRoutine : Routine 40 := sequence readTarget (sequence readSource
  (sequence axpyRows (sequence writeRow cleanup)))

theorem readTarget_executes (factor sourceIndex : List Bool) (rows : List (List Rat)) (target : Fin rows.length) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(target.val+1)+14,
      Executes readTarget (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (target.val+1) true)
        sourceIndex [] [] [] [] []) time
        (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (target.val+1) true)
          sourceIndex (Encoding.rationalRow.encode rows[target.val]) [] [] [true] []) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 34 targetRoles
    (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (target.val+1) true) sourceIndex [] [] [] [] [])
    rows target.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r;fin_cases r <;> simp [file,targetRoles,RowAxpy.file,target.isLt]

theorem readSource_executes (factor targetIndex target : List Bool) (rows : List (List Rat)) (source : Fin rows.length) :
    ∃ time ≤ 10*(Encoding.rationalMatrix.encode rows).length+8*(source.val+1)+14,
      Executes readSource (file factor (Encoding.rationalMatrix.encode rows) targetIndex
        (List.replicate (source.val+1) true) target [] [] [true] []) time
        (file factor (Encoding.rationalMatrix.encode rows) targetIndex (List.replicate (source.val+1) true)
          target (Encoding.rationalRow.encode rows[source.val]) [] [true] [true]) := by
  obtain ⟨time,bounded,ran⟩ := preservingRead_framedList_executes Encoding.rationalRow 34 sourceRoles
    (file factor (Encoding.rationalMatrix.encode rows) targetIndex (List.replicate (source.val+1) true) target [] [] [true] [])
    rows source.val rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r;fin_cases r <;> simp [file,sourceRoles,RowAxpy.file,source.isLt]

theorem axpyRows_executes (factor : Rat) (target source : List Rat) (sameLength : target.length=source.length)
    (matrix targetIndex sourceIndex : List Bool) :
    ∃ time ≤ RowAxpy.costConstant*((Encoding.rational.encode factor).length+
      (Encoding.rationalRow.encode target).length+(Encoding.rationalRow.encode source).length+1)^16,
      Executes axpyRows (file (Encoding.rational.encode factor) matrix targetIndex sourceIndex
        (Encoding.rationalRow.encode target) (Encoding.rationalRow.encode source) [] [true] [true]) time
        (file (Encoding.rational.encode factor) matrix targetIndex sourceIndex [] []
          (Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) target source)) [true] [true]) := by
  have mapped : (target.zip source).map (fun pair=>pair.1+factor*pair.2)=List.zipWith (fun a b=>a+factor*b) target source := by
    rw [List.map_zip_eq_zipWith];rfl
  obtain ⟨time,bounded,ran⟩ := RowAxpy.axpy_executes_polynomial factor (target.zip source)
  simp only [List.map_fst_zip sameLength.le,List.map_snd_zip sameLength.ge,mapped] at bounded ran
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RowAxpy.axpyRoutine rowRoles _ _ _ _ time _ _ _ ran
  · funext r;simp [file,rowRoles,r.isLt]
  · intro r;simp [file,rowRoles,r.isLt]
  · intro r outside
    have large : ¬r.val<37 := by
      intro small;exact outside ⟨r.val,small⟩ (Fin.ext rfl)
    simp only [file,dif_neg large]

theorem writeRow_executes (factor sourceIndex : List Bool) (rows : List (List Rat))
    (target : Fin rows.length) (replacement : List Rat) :
    ∃ time ≤ 5*(Encoding.rationalMatrix.encode rows).length+3*(target.val+1)+
      17*(Encoding.rationalRow.encode replacement).length+21,
      Executes writeRow (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (target.val+1) true)
        sourceIndex [] [] (Encoding.rationalRow.encode replacement) [true] [true]) time
        (file factor (Encoding.rationalMatrix.encode (rows.set target.val replacement)) [] sourceIndex [] [] [] [true] [true]) := by
  obtain ⟨time,bounded,ran⟩ := writePayload_framedList_executes Encoding.rationalRow 36 writeRoles
    (file factor (Encoding.rationalMatrix.encode rows) (List.replicate (target.val+1) true)
      sourceIndex [] [] (Encoding.rationalRow.encode replacement) [true] [true])
    rows target.val replacement target.isLt rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  convert ran using 1
  funext r;fin_cases r <;> simp [file,writeRoles,RowAxpy.file,Encoding.rationalMatrix]

theorem cleanup_executes (factor matrix sourceIndex : List Bool) :
    Executes cleanup (file factor matrix [] sourceIndex [] [] [] [true] [true]) (sourceIndex.length+7)
      (file factor matrix [] [] [] [] [] [] []) := by
  let first := file factor matrix [] sourceIndex [] [] [] [true] [true]
  let second := file factor matrix [] [] [] [] [] [true] [true]
  let third := file factor matrix [] [] [] [] [] [] [true]
  have a := clear_executes (39 : Fin 42) first
  have ra : Function.update first 39 []=second := by funext r;fin_cases r <;> simp [first,second,file,RowAxpy.file]
  rw [ra] at a
  have b := clear_executes (40 : Fin 42) second
  have rb : Function.update second 40 []=third := by funext r;fin_cases r <;> simp [second,third,file,RowAxpy.file]
  rw [rb] at b
  have c := clear_executes (41 : Fin 42) third
  have rc : Function.update third 41 []=file factor matrix [] [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [third,file,RowAxpy.file]
  rw [rc] at c
  change Executes _ first (sourceIndex.length+1) second at a
  change Executes _ second 2 third at b
  change Executes _ third 2 _ at c
  convert a.sequence (b.sequence c) using 1

/-- Identical source and destination indices are allowed: both reads occur
before the matrix update, so the resulting row is `(1+factor)` times the old row. -/
theorem axpy_executes (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    ∃ time ≤ 25*(Encoding.rationalMatrix.encode rows).length+11*(target.val+1)+9*(source.val+1)+
      RowAxpy.costConstant*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode rows[target.val]).length+
        (Encoding.rationalRow.encode rows[source.val]).length+1)^16+
      17*(Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val])).length+70,
      Executes axpyRoutine (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
        (List.replicate (target.val+1) true) (List.replicate (source.val+1) true) [] [] [] [] []) time
        (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode
          (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))) [] [] [] [] [] [] []) := by
  obtain ⟨a,ha,ra⟩ := readTarget_executes (Encoding.rational.encode factor) (List.replicate (source.val+1) true) rows target
  obtain ⟨b,hb,rb⟩ := readSource_executes (Encoding.rational.encode factor) (List.replicate (target.val+1) true)
    (Encoding.rationalRow.encode rows[target.val]) rows source
  obtain ⟨c,hc,rc⟩ := axpyRows_executes factor rows[target.val] rows[source.val] sameLength (Encoding.rationalMatrix.encode rows)
    (List.replicate (target.val+1) true) (List.replicate (source.val+1) true)
  obtain ⟨d,hd,rd⟩ := writeRow_executes (Encoding.rational.encode factor) (List.replicate (source.val+1) true) rows target
    (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val])
  have cleaned := cleanup_executes (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode
    (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))) (List.replicate (source.val+1) true)
  refine ⟨_,?_,ra.sequence (rb.sequence (rc.sequence (rd.sequence cleaned)))⟩
  simp only [List.length_replicate]
  omega

end Counting.StackMachine.MatrixAxpy
