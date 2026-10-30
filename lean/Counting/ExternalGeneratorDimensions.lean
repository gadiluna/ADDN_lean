import Counting.ExternalGeneratorWorkspace

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def offsetRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 2) (w 31))) (pushBit (w 2) true)

theorem offsetRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (time : Nat)
    (store : Fin (extra+32) → List Bool) (timeValue : store (w 0)=List.replicate time true)
    (offsetEmpty : store (w 2)=[]) (workEmpty : store (w 31)=[]) :
    Executes (offsetRoutine extra w) store (5*time+4)
      (Function.update store (w 2) (List.replicate (time+1) true)) := by
  have copied := copy_executes (extra+29) (w 0) (w 2) (w 31)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store workEmpty
  have normalized : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 2) (w 31))) store (5*time+2)
      (Function.update store (w 2) (List.replicate time true)) := by
    simpa +instances only [ListPrograms.copyProgram,timeValue,offsetEmpty,List.length_replicate,List.append_nil] using copied
  have combined := normalized.sequence (pushBit_executes (w 2) true (Function.update store (w 2) (List.replicate time true)))
  simpa +instances only [offsetRoutine,ListPrograms.copyProgram,Function.update_self,Function.update_idem,List.replicate_succ,
    show 5*time+2+1+1=5*time+4 by omega] using combined

def widthRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+30) :=
  sequence (scaleLength (extra+29) (w 2) (w 1) (w 31) 2)
    (ofProgram (ListPrograms.copyProgram (extra+29) (w 29) (w 1) (w 31)))

theorem widthRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (offset timeBase : Nat)
    (store : Fin (extra+32) → List Bool)
    (offsetValue : store (w 2)=List.replicate offset true) (timeBaseValue : store (w 29)=List.replicate timeBase true)
    (widthEmpty : store (w 1)=[]) (workEmpty : store (w 31)=[]) :
    Executes (widthRoutine extra w) store (10*offset+5*timeBase+9)
      (Function.update store (w 1) (List.replicate (timeBase+2*offset) true)) := by
  let measured := Function.update store (w 1) (List.replicate (2*offset) true)
  have scaled := scaleLength_executes (extra+29) (w 2) (w 1) (w 31)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 2 store workEmpty
  have first : Executes (scaleLength (extra+29) (w 2) (w 1) (w 31) 2) store (2*(5*offset+3)) measured := by
    simpa only [measured,offsetValue,widthEmpty,List.append_nil,List.length_replicate] using scaled
  have copied := copy_executes (extra+29) (w 29) (w 1) (w 31)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) measured
    (by simp [measured,w.injective.eq_iff,workEmpty])
  have second : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 29) (w 1) (w 31))) measured (5*timeBase+2)
      (Function.update store (w 1) (List.replicate (timeBase+2*offset) true)) := by
    simpa +instances [ListPrograms.copyProgram,measured,w.injective.eq_iff,timeBaseValue,← List.replicate_add] using copied
  simpa +instances only [widthRoutine,ListPrograms.copyProgram,
    show 2*(5*offset+3)+1+(5*timeBase+2)=10*offset+5*timeBase+9 by omega] using first.sequence second

def generatorCellsSelection : Fin 6 ↪ Fin 32 := ⟨![2,1,6,26,27,31],by decide⟩
def GeneratorWorkspace.cellsRoles (w : GeneratorWorkspace extra) : PolynomialWorkspace (extra+26) := generatorCellsSelection.trans w

def cellsRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+30) :=
  centerRoutine (extra+26) w.cellsRoles

theorem cellsRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (offset width : Nat)
    (store : Fin (extra+32) → List Bool)
    (offsetValue : store (w 2)=List.replicate offset true) (widthValue : store (w 1)=List.replicate width true)
    (zeroValue : store (w 6)=[]) (cellsEmpty : store (w 26)=[]) (counterEmpty : store (w 27)=[]) (workEmpty : store (w 31)=[]) :
    Executes (cellsRoutine extra w) store ((5*width+9)*offset+7)
      (Function.update store (w 26) (List.replicate (offset*width) true)) := by
  have run := centerRoutine_executes (extra+26) w.cellsRoles offset width 0 store
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using offsetValue)
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using widthValue)
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using zeroValue)
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using cellsEmpty)
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using counterEmpty)
    (by simpa [GeneratorWorkspace.cellsRoles,generatorCellsSelection] using workEmpty)
  simpa [cellsRoutine,GeneratorWorkspace.cellsRoles,generatorCellsSelection,centerCost] using run

end Counting.External.CookLevin.StackGenerator
