import Counting.StackRealizabilityRoundFile
import Counting.StackDagIncrement

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def roundPrepare : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 83 84 0))
  (sequence (DagValidation.incrementRoutine 97 0 84 2)
    (ofProgram (ListPrograms.copyProgram 97 80 86 0)))

theorem roundPrepare_executes (data : Fin 20→List Bool) (round : Nat)
    (roundAt : data 3=round.bits) (e4 : data 4=[]) (e6 : data 6=[]) :
    ∃ time ≤ 20*((data 0).length+round.size+1),
      Executes roundPrepare (roundFile data) time
        (roundFile (Function.update (Function.update data 4 (round+1).bits) 6 (data 0))) := by
  have copying := copy_executes 97 83 84 0 (by decide) (by decide) (by decide) (roundFile data)
    (by simp [roundFile])
  have inputAt : roundFile data 83=round.bits := by simpa [roundFile] using roundAt
  have targetAt : roundFile data 84=[] := by simpa [roundFile] using e4
  rw [inputAt,targetAt,List.append_nil] at copying
  let copied := Function.update (roundFile data) 84 round.bits
  obtain ⟨incrementTime,incrementBound,incrementing⟩ := DagValidation.increment_natural 97 0 84 2
    (by decide) (by decide) (by decide) copied (by simp [copied,roundFile])
    (by simp [copied,roundFile]) round (by simp [copied])
  let next := Function.update copied 84 (round+1).bits
  have sourceCopy := copy_executes 97 80 86 0 (by decide) (by decide) (by decide) next
    (by simp [next,copied,roundFile])
  have sourceAt : next 80=data 0 := by simp [next,copied,roundFile]
  have emptyAt : next 86=[] := by simp [next,copied,roundFile,e6]
  rw [sourceAt,emptyAt,List.append_nil] at sourceCopy
  have final : Function.update next 86 (data 0)=
      roundFile (Function.update (Function.update data 4 (round+1).bits) 6 (data 0)) := by
    simp only [next,copied,Function.update_idem]
    change Function.update (Function.update (roundFile data) (roundContext 4) (round+1).bits)
      (roundContext 6) (data 0)=_
    rw [roundFile_update,roundFile_update]
  rw [final] at sourceCopy
  have execution := copying.sequence (incrementing.sequence sourceCopy)
  simp only [Encoding.bits_length] at execution
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
