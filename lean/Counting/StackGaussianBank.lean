import Counting.StackMatrixAxpyBounds
import Counting.StackMatrixScaleBounds
import Counting.StackGaussianEntry

/-! A fixed register bank shared by the three serialized matrix operations.
The ten persistent registers are explicitly outside every matrix workspace.
Register relocation changes code addresses only and costs no extra machine
steps; the existing operations still execute every read and replacement. -/
namespace Counting.StackMachine.GaussianBank
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Registers 42..51 are, respectively, the pivot, dimension, candidate,
status, reversed transcript, transcript count, row, loop count, and two
temporary fields. Their interpretation is not needed by matrix operations. -/
def bank (workspace : Fin 42 → List Bool) (saved : Fin 10 → List Bool) : Fin 52 → List Bool :=
  fun r => if small : r.val < 42 then workspace ⟨r.val,small⟩
    else saved ⟨r.val-42,by omega⟩

def ready (matrix factor first second : List Bool) (saved : Fin 10 → List Bool) : Fin 52 → List Bool :=
  bank (MatrixAxpy.file factor matrix first second [] [] [] [] []) saved

def workspaceRoles : Fin 42 ↪ Fin 52 := ⟨fun r => r.castLE (by decide),by
  intro a b equal
  exact Fin.ext (congrArg (fun r : Fin 52 => r.val) equal)⟩

def swapRoles : Fin 10 ↪ Fin 52 := ⟨![37,38,39,1,2,40,4,5,6,7],by decide⟩

def scaleRoles : Fin 35 ↪ Fin 52 := ⟨fun r =>
  if r.val < 32 then ⟨r.val,by omega⟩
  else if r=32 then 37 else if r=33 then 38 else 40,by
  intro a b equal
  fin_cases a <;> fin_cases b <;> simp_all⟩

abbrev swap : Routine 50 := relocate MatrixSwap.swapRoutine swapRoles
abbrev scale : Routine 50 := relocate MatrixScale.scaleRoutine scaleRoles
abbrev add : Routine 50 := relocate MatrixAxpy.axpyRoutine workspaceRoles

theorem swap_executes (rows : List (List Rat)) (first second : Fin rows.length)
    (factor : List Bool) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 100*((Encoding.rationalMatrix.encode rows).length+1),
      Executes swap
        (ready (Encoding.rationalMatrix.encode rows) factor (List.replicate (first.val+1) true)
          (List.replicate (second.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
          factor [] [] saved) := by
  obtain ⟨time,bounded,ran⟩ := MatrixSwap.swap_executes_linear rows first second
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame MatrixSwap.swapRoutine swapRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [ready,bank,swapRoles,MatrixAxpy.file,RowAxpy.file,MatrixSwap.file]
  · intro r;fin_cases r <;> simp [ready,bank,swapRoles,MatrixAxpy.file,RowAxpy.file,MatrixSwap.file]
  · intro r outside
    have matrix := outside 0
    have firstIndex := outside 1
    have secondIndex := outside 2
    fin_cases r <;> simp_all [ready,bank,swapRoles,MatrixAxpy.file,RowAxpy.file]

theorem scale_executes (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length)
    (saved : Fin 10 → List Bool) :
    ∃ time ≤ 60000000000*(2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2)^4,
      Executes scale
        (ready (Encoding.rationalMatrix.encode rows) (Encoding.rational.encode factor)
          (List.replicate (index.val+1) true) [] saved) time
        (ready (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·))))
          (Encoding.rational.encode factor) [] [] saved) := by
  obtain ⟨time,bounded,ran⟩ := MatrixScale.scale_executes_polynomial factor rows index
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame MatrixScale.scaleRoutine scaleRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [ready,bank,scaleRoles,MatrixAxpy.file,RowAxpy.file,MatrixScale.file,RowScale.file]
  · intro r;fin_cases r <;> simp [ready,bank,scaleRoles,MatrixAxpy.file,RowAxpy.file,MatrixScale.file,RowScale.file]
  · intro r outside
    have matrix := outside 32
    have firstIndex := outside 33
    fin_cases r <;> simp_all [ready,bank,scaleRoles,MatrixAxpy.file,RowAxpy.file]

theorem add_executes (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) (saved : Fin 10 → List Bool) :
    ∃ time ≤ MatrixAxpy.costConstant*(MatrixAxpy.sizeBound factor rows)^16,
      Executes add
        (ready (Encoding.rationalMatrix.encode rows) (Encoding.rational.encode factor)
          (List.replicate (target.val+1) true) (List.replicate (source.val+1) true) saved) time
        (ready (Encoding.rationalMatrix.encode
          (rows.set target.val (List.zipWith (fun a b => a+factor*b) rows[target.val] rows[source.val])))
          (Encoding.rational.encode factor) [] [] saved) := by
  obtain ⟨time,bounded,ran⟩ := MatrixAxpy.axpy_executes_polynomial factor rows target source sameLength
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame MatrixAxpy.axpyRoutine workspaceRoles _ _ _ _ time _ _ _ ran
  · funext r;simp [ready,bank,workspaceRoles,r.isLt]
  · intro r;simp [ready,bank,workspaceRoles,r.isLt]
  · intro r outside
    have large : ¬r.val < 42 := by
      intro small
      exact outside ⟨r.val,small⟩ (Fin.ext rfl)
    simp only [ready,bank,dif_neg large]

end Counting.StackMachine.GaussianBank
