import Counting.StackRealizabilityCallFile
import Counting.StackRoutineLists

namespace Counting.StackMachine.RealizabilityCall
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def clearExternal (target : Fin 30) : Routine 128 := clear (context target)

theorem clearExternal_executes (data : Fin 30→List Bool) (target : Fin 30) :
    Executes (clearExternal target) (file data) ((data target).length+1)
      (file (Function.update data target [])) := by
  have run := clear_executes (context target) (file data)
  rw [file_context,file_update] at run
  exact run

def copyExternal (source target : Fin 30) : Routine 128 :=
  ofProgram (ListPrograms.copyProgram 127 (context source) (context target) 0)

theorem copyExternal_executes (data : Fin 30→List Bool) (source target : Fin 30)
    (distinct : source≠target) :
    Executes (copyExternal source target) (file data) (5*(data source).length+2)
      (file (Function.update data target (data source++data target))) := by
  have workDifferent (r : Fin 30) : context r≠0 := by
    intro same
    have := congrArg (fun i:Fin 130=>i.val) same
    change 100+r.val=0 at this
    omega
  have run := copy_executes 127 (context source) (context target) 0
    (fun same=>distinct (context.injective same)) (workDifferent source) (workDifferent target)
    (file data) (by simp [file])
  rw [file_context,file_context,file_update] at run
  exact run

end Counting.StackMachine.RealizabilityCall
