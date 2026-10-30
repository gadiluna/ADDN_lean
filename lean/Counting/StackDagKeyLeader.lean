import Counting.StackEncodingBranch
import Counting.StackRoutineBasic
import Counting.EncodingBinary

namespace Counting.StackMachine.DagUpdate.Key
open Routine EncodingPrograms

def emitLeader (source target : Fin (registers+2)) : Routine registers :=
  branchRoutine source (prepend target [true,true,false]) (prepend target [false])

theorem emitLeader_executes (source target : Fin (registers+2)) (different : source≠target)
    (store : Store registers) (leader : Bool) (input : store source=[leader]) :
    Executes (emitLeader source target) store
      (1+2*(Encoding.natural.encode (if leader then 1 else 0)).length)
      (Function.update (Function.update store source []) target
        (Encoding.natural.encode (if leader then 1 else 0)++store target)) := by
  let consumed := Function.update store source []
  have pushing := prepend_executes target (Encoding.natural.encode (if leader then 1 else 0)) consumed
  have unchanged : consumed target=store target := by simp [consumed,different.symm]
  rw [unchanged] at pushing
  cases leader
  · exact branch_executes_false source _ _ store _ [] 2 input pushing
  · exact branch_executes_true source _ _ store _ [] 6 input pushing

end Counting.StackMachine.DagUpdate.Key
