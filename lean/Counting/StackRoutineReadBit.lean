import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine
open EncodingPrograms

def readBit (source target : Fin (registers+2)) : Routine registers :=
  branchRoutine source (pushBit target true) (pushBit target false)

theorem readBit_executes (source target : Fin (registers+2)) (different : source≠target)
    (store : Store registers) (bit : Bool) (suffix : List Bool) (input : store source=bit::suffix) :
    Executes (readBit source target) store 2
      (Function.update (Function.update store source suffix) target (bit::store target)) := by
  let consumed:=Function.update store source suffix
  have pushing:=pushBit_executes target bit consumed
  have unchanged : consumed target=store target := by simp [consumed,different.symm]
  rw [unchanged] at pushing
  cases bit
  · exact branch_executes_false source _ _ store _ suffix 1 input pushing
  · exact branch_executes_true source _ _ store _ suffix 1 input pushing

end Counting.StackMachine.Routine
