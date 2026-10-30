import Counting.StackRealizabilityCallFile
import Counting.StackRoutineLists

namespace Counting.StackMachine.RealizabilityCall
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

def copyField (i : Fin 30) : Routine 128 := ofProgram (ListPrograms.copyProgram 127 (context i) 0 2)

theorem copyField_executes (data : Fin 30→List Bool) (i : Fin 30) (input : List Bool) :
    Executes (copyField i) (Function.update (file data) 0 input) (5*(data i).length+2)
      (Function.update (file data) 0 (data i++input)) := by
  have a : context i≠0 := by intro same;have:=congrArg Fin.val same;change 100+i.val=0 at this;omega
  have b : context i≠2 := by intro same;have:=congrArg Fin.val same;change 100+i.val=2 at this;omega
  let start := Function.update (file data) 0 input
  have run := copy_executes 127 (context i) 0 2 a b (by decide) start (by simp [start,file])
  have sourceAt : start (context i)=data i := by simp [start,a]
  have outputAt : start 0=input := by simp [start]
  rw [sourceAt,outputAt] at run
  change Executes (copyField i) start (5*(data i).length+2)
    (Function.update start 0 (data i++input)) at run
  simpa only [start,Function.update_idem] using run

def encodedInput (data : Fin 30→List Bool) : List Bool := data 0++data 1++data 2++data 3

def copyInputs : Routine 128 := sequence (copyField 3)
  (sequence (copyField 2) (sequence (copyField 1) (copyField 0)))

/-- Tuple assembly copies the exact saved codes in the required order.
It neither assumes them canonical nor rebuilds their numeric values. -/
theorem copyInputs_executes (data : Fin 30→List Bool) :
    Executes copyInputs (file data) (5*(encodedInput data).length+11)
      (Function.update (file data) 0 (encodedInput data)) := by
  have r0 := copyField_executes data 3 []
  have empty : file data 0=[] := by simp [file]
  have startEq : Function.update (file data) (0:Fin 130) []=file data := by
    rw [←empty,Function.update_eq_self]
  rw [startEq,List.append_nil] at r0
  have r1 := copyField_executes data 2 (data 3)
  have r2 := copyField_executes data 1 (data 2++data 3)
  have r3 := copyField_executes data 0 (data 1++(data 2++data 3))
  have r3final : Executes (copyField 0)
      (Function.update (file data) 0 (data 1++(data 2++data 3))) (5*(data 0).length+2)
      (Function.update (file data) 0 (encodedInput data)) := by
    simpa only [encodedInput,List.append_assoc] using r3
  have combined : Executes copyInputs (file data)
      (5*(data 3).length+2+1+(5*(data 2).length+2+1+
        (5*(data 1).length+2+1+(5*(data 0).length+2))))
      (Function.update (file data) 0 (encodedInput data)) := r0.sequence (r1.sequence (r2.sequence r3final))
  have time : 5*(data 3).length+2+1+(5*(data 2).length+2+1+
        (5*(data 1).length+2+1+(5*(data 0).length+2)))=5*(encodedInput data).length+11 := by
    simp only [encodedInput,List.length_append];omega
  simpa only [time] using combined

end Counting.StackMachine.RealizabilityCall
