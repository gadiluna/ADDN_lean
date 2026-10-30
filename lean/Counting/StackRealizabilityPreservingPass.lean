import Counting.StackRoutineLists
import Counting.StackRoutineBasic

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Repeated certificate scans use preserved originals in registers 34 and 35.
Registers 17 and 20 receive physical copies; register 33 is copy scratch. -/
def preservedPass (body : Routine 34) : Routine 34:=
  sequence (ofProgram (ListPrograms.copyProgram 33 34 17 33))
    (sequence (ofProgram (ListPrograms.copyProgram 33 35 20 33))
      (sequence body (sequence (clear 17) (clear 20))))

def preparedPassStore (store : Store 34) : Store 34:=
  Function.update (Function.update store 17 (store 34)) 20 (store 35)

def finishedPassStore (result : Store 34) : Store 34:=
  Function.update (Function.update result 17 []) 20 []

/-- The copying and cleanup are charged explicitly. The body contract is
used compositionally and is instantiated by the concrete scan theorems. -/
theorem preservedPass_executes (body : Routine 34) (store result : Store 34) (time : Nat)
    (e17 : store 17=[]) (e20 : store 20=[]) (e33 : store 33=[])
    (bodyRun : Executes body (preparedPassStore store) time result) :
    Executes (preservedPass body) store
      (time+5*((store 34).length+(store 35).length)+(result 17).length+(result 20).length+10)
      (finishedPassStore result):=by
  have first:=copy_executes 33 34 17 33 (by decide) (by decide) (by decide) store e33
  rw [e17,List.append_nil] at first
  let copied:=Function.update store 17 (store 34)
  have second:=copy_executes 33 35 20 33 (by decide) (by decide) (by decide) copied
    (by simp [copied,e33])
  have source : copied 35=store 35:=by simp [copied]
  have destination : copied 20=[]:=by simp [copied,e20]
  rw [source,destination,List.append_nil] at second
  have clearNodes:=clear_executes (17:Fin 36) result
  let noNodes:=Function.update result 17 []
  have clearWeights:=clear_executes (20:Fin 36) noNodes
  have remaining : noNodes 20=result 20:=by simp [noNodes]
  rw [remaining] at clearWeights
  have completed:=first.sequence (second.sequence (bodyRun.sequence (clearNodes.sequence clearWeights)))
  convert completed using 1 <;> first | rfl | omega

end Counting.StackMachine.RealizabilityCheck
