import Counting.StackGaussianState
import Counting.StackGaussianTranscript

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

def pivotLogRoles : GaussianTranscript.Workspace 43 := ⟨![42,44,0,46,47,1,2,3,4],by decide⟩
def rowLogRoles : GaussianTranscript.Workspace 43 := ⟨![48,42,0,46,47,1,2,3,4],by decide⟩

def logSaved (saved : Fin 10 → List Bool) (operation : RawRowOp) : Fin 10 → List Bool :=
  Function.update (Function.update saved 4 (Encoding.frame (Encoding.rawRowOp.encode operation)++saved 4))
    5 (true::saved 5)

abbrev recordSwap : Routine 50 := GaussianTranscript.emit .swap 43 pivotLogRoles
abbrev recordScale : Routine 50 := GaussianTranscript.emit .scale 43 pivotLogRoles
abbrev recordAdd : Routine 50 := GaussianTranscript.emit .add 43 rowLogRoles

theorem recordSwap_executes (matrix factor : List Bool) (pivot row : Nat) (saved : Fin 10 → List Bool)
    (hp : saved 0=List.replicate (pivot+1) true) (hr : saved 2=List.replicate (row+1) true) :
    ∃ time ≤ 200*(pivot+row+15)^2,
      Executes recordSwap (ready matrix factor [] [] saved) time
        (ready matrix factor [] [] (logSaved saved (.swap pivot row))) := by
  obtain ⟨time,bounded,ran⟩ := GaussianTranscript.emit_operation_executes .swap 43 pivotLogRoles
    (ready matrix factor [] [] saved) pivot row 0
    (by simpa [pivotLogRoles,ready,bank] using hp)
    (by intro _;simpa [pivotLogRoles,ready,bank] using hr)
    (by simp) rfl rfl rfl rfl
  refine ⟨time,?_,?_⟩
  · simpa [GaussianTranscript.factorWord,Encoding.rational_length] using bounded
  · convert ran using 1
    funext r;fin_cases r <;> simp [GaussianTranscript.result,GaussianTranscript.Kind.operation,
      logSaved,pivotLogRoles,ready,bank,MatrixAxpy.file,RowAxpy.file]

theorem recordScale_executes (matrix : List Bool) (factor : Rat) (pivot : Nat) (saved : Fin 10 → List Bool)
    (hp : saved 0=List.replicate (pivot+1) true) :
    ∃ time ≤ 200*(pivot+(Encoding.rational.encode factor).length+10)^2,
      Executes recordScale (ready matrix (Encoding.rational.encode factor) [] [] saved) time
        (ready matrix (Encoding.rational.encode factor) [] [] (logSaved saved (.scale pivot factor))) := by
  obtain ⟨time,bounded,ran⟩ := GaussianTranscript.emit_operation_executes .scale 43 pivotLogRoles
    (ready matrix (Encoding.rational.encode factor) [] [] saved) pivot 0 factor
    (by simpa [pivotLogRoles,ready,bank] using hp) (by simp) (by intro _;rfl) rfl rfl rfl rfl
  refine ⟨time,?_,?_⟩
  · simpa [GaussianTranscript.factorWord,pivotLogRoles,ready,bank,MatrixAxpy.file,RowAxpy.file] using bounded
  · convert ran using 1
    funext r;fin_cases r <;> simp [GaussianTranscript.result,GaussianTranscript.Kind.operation,
      logSaved,pivotLogRoles,ready,bank,MatrixAxpy.file,RowAxpy.file]

theorem recordAdd_executes (matrix : List Bool) (factor : Rat) (target source : Nat) (saved : Fin 10 → List Bool)
    (ht : saved 6=List.replicate (target+1) true) (hs : saved 0=List.replicate (source+1) true) :
    ∃ time ≤ 200*(target+source+(Encoding.rational.encode factor).length+10)^2,
      Executes recordAdd (ready matrix (Encoding.rational.encode factor) [] [] saved) time
        (ready matrix (Encoding.rational.encode factor) [] [] (logSaved saved (.add target source factor))) := by
  obtain ⟨time,bounded,ran⟩ := GaussianTranscript.emit_operation_executes .add 43 rowLogRoles
    (ready matrix (Encoding.rational.encode factor) [] [] saved) target source factor
    (by simpa [rowLogRoles,ready,bank] using ht)
    (by intro _;simpa [rowLogRoles,ready,bank] using hs) (by intro _;rfl) rfl rfl rfl rfl
  refine ⟨time,?_,?_⟩
  · simpa [GaussianTranscript.factorWord,rowLogRoles,ready,bank,MatrixAxpy.file,RowAxpy.file] using bounded
  · convert ran using 1
    funext r;fin_cases r <;> simp [GaussianTranscript.result,GaussianTranscript.Kind.operation,
      logSaved,rowLogRoles,ready,bank,MatrixAxpy.file,RowAxpy.file]

theorem logSaved_stateSaved {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter flag : List Bool) (operation : RowOp q) :
    logSaved (stateSaved state pivot candidate row counter flag) (RawRowOp.ofRowOp operation)=
      stateSaved (StoredGaussian.emit state operation) pivot candidate row counter flag := by
  funext r;fin_cases r <;> simp [logSaved,stateSaved,StoredGaussian.emit,List.replicate_succ]

end Counting.StackMachine.GaussianBank
