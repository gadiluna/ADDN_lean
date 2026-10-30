import Counting.StackGaussianBank
import Counting.StackComparePreserving

namespace Counting.StackMachine.GaussianBank
open Routine
set_option backward.isDefEq.respectTransparency false

def savedRole (index : Fin 10) : Fin 52 := ⟨index.val+42,by omega⟩

@[simp] theorem bank_saved (workspace : Fin 42 → List Bool) (saved : Fin 10 → List Bool) (index : Fin 10) :
    bank workspace saved (savedRole index)=saved index := by
  simp [bank,savedRole]

@[simp] theorem ready_saved (matrix factor first second : List Bool) (saved : Fin 10 → List Bool) (index : Fin 10) :
    ready matrix factor first second saved (savedRole index)=saved index := bank_saved _ _ _

theorem update_saved (matrix factor first second : List Bool) (saved : Fin 10 → List Bool)
    (index : Fin 10) (value : List Bool) :
    Function.update (ready matrix factor first second saved) (savedRole index) value=
      ready matrix factor first second (Function.update saved index value) := by
  funext r
  by_cases small : r.val < 42
  · have different : r≠savedRole index := by intro equal;have := congrArg Fin.val equal;simp only [savedRole] at this;omega
    simp [Function.update_of_ne different,ready,bank,small]
  · have equal : r=savedRole index ↔ (⟨r.val-42,by omega⟩ : Fin 10)=index := by
      simp only [Fin.ext_iff,savedRole];omega
    simp only [ready,bank,dif_neg small,Function.update_apply,equal]

abbrev loadFirst (source : Fin 10) : Routine 50 := ofProgram (ListPrograms.copyProgram 49 (savedRole source) 38 1)
abbrev loadSecond (source : Fin 10) : Routine 50 := ofProgram (ListPrograms.copyProgram 49 (savedRole source) 39 1)

theorem loadFirst_executes (source : Fin 10) (matrix factor second : List Bool) (saved : Fin 10 → List Bool) :
    Executes (loadFirst source) (ready matrix factor [] second saved) (5*(saved source).length+2)
      (ready matrix factor (saved source) second saved) := by
  have ran := copy_executes 49 (savedRole source) 38 1 (by simp [savedRole,Fin.ext_iff])
    (by simp [savedRole,Fin.ext_iff]) (by decide) (ready matrix factor [] second saved) rfl
  rw [ready_saved] at ran
  simp +instances only [ListPrograms.copyProgram] at ran
  convert ran using 1
  · rfl
  · funext r;fin_cases r <;> simp [ready,bank,MatrixAxpy.file,RowAxpy.file]

theorem loadSecond_executes (source : Fin 10) (matrix factor first : List Bool) (saved : Fin 10 → List Bool) :
    Executes (loadSecond source) (ready matrix factor first [] saved) (5*(saved source).length+2)
      (ready matrix factor first (saved source) saved) := by
  have ran := copy_executes 49 (savedRole source) 39 1 (by simp [savedRole,Fin.ext_iff])
    (by simp [savedRole,Fin.ext_iff]) (by decide) (ready matrix factor first [] saved) rfl
  rw [ready_saved] at ran
  simp +instances only [ListPrograms.copyProgram] at ran
  convert ran using 1
  · rfl
  · funext r;fin_cases r <;> simp [ready,bank,MatrixAxpy.file,RowAxpy.file]

abbrev loadPair (first second : Fin 10) : Routine 50 := sequence (loadFirst first) (loadSecond second)

theorem loadPair_executes (first second : Fin 10) (matrix factor : List Bool) (saved : Fin 10 → List Bool) :
    Executes (loadPair first second) (ready matrix factor [] [] saved)
      (5*(saved first).length+5*(saved second).length+5)
      (ready matrix factor (saved first) (saved second) saved) := by
  convert (loadFirst_executes first matrix factor [] saved).sequence
    (loadSecond_executes second matrix factor (saved first) saved) using 1
  omega

theorem clearFactor_executes (matrix factor first second : List Bool) (saved : Fin 10 → List Bool) :
    Executes (clear (0 : Fin 52)) (ready matrix factor first second saved) (factor.length+1)
      (ready matrix [] first second saved) := by
  have ran := clear_executes (0 : Fin 52) (ready matrix factor first second saved)
  change Executes _ _ (factor.length+1) _ at ran
  convert ran using 1
  funext r;fin_cases r <;> simp [ready,bank,MatrixAxpy.file,RowAxpy.file]

def comparisonRoles : Fin 6 ↪ Fin 52 := ⟨![42,48,50,1,2,3],by decide⟩
abbrev compareRow : Routine 50 := Compare.preservingEquality 46 comparisonRoles

theorem compareRow_executes (matrix : List Bool) (saved : Fin 10 → List Bool) (empty : saved 8=[]) :
    Executes compareRow (ready matrix [] [] [] saved) (Compare.preservingCost (saved 0) (saved 6))
      (ready matrix [] [] [] (Function.update saved 8 [decide (saved 0=saved 6)])) := by
  have ran := Compare.preservingEquality_executes 46 comparisonRoles (ready matrix [] [] [] saved) rfl rfl rfl
  have first : ready matrix [] [] [] saved (comparisonRoles 0)=saved 0 := by simp [comparisonRoles,ready,bank]
  have second : ready matrix [] [] [] saved (comparisonRoles 1)=saved 6 := by simp [comparisonRoles,ready,bank]
  rw [first,second] at ran
  convert ran using 1
  funext r;fin_cases r <;> simp [comparisonRoles,ready,bank,MatrixAxpy.file,RowAxpy.file,empty]

end Counting.StackMachine.GaussianBank
