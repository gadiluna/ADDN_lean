import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine
open EncodingPrograms

/-- Branch on a canonical unary counter without changing it. Restoring the
consumed true marker is an actual push and its sequencing jump is charged. -/
def branchUnary {registers : Nat} (counter : Fin (registers+2)) (nonzero zero : Routine registers) : Routine registers :=
  branchRoutine counter (sequence (pushBit counter true) nonzero) zero

theorem branchUnary_zero {registers : Nat} (counter : Fin (registers+2)) (nonzero zero : Routine registers)
    (store result : Store registers) (time : Nat) (empty : store counter=[])
    (executed : Executes zero store time result) :
    Executes (branchUnary counter nonzero zero) store (1+time) result :=
  branch_executes_empty counter _ _ store result time empty executed

theorem branchUnary_nonzero {registers : Nat} (counter : Fin (registers+2)) (nonzero zero : Routine registers)
    (store result : Store registers) (tail : List Bool) (time : Nat) (nonempty : store counter=true::tail)
    (executed : Executes nonzero store time result) :
    Executes (branchUnary counter nonzero zero) store (time+3) result := by
  have restored := pushBit_executes counter true (Function.update store counter tail)
  have equal : Function.update (Function.update store counter tail) counter
      (true::Function.update store counter tail counter) = store := by
    rw [Function.update_self,Function.update_idem,← nonempty,Function.update_eq_self]
  rw [equal] at restored
  have combined := restored.sequence executed
  have run := branch_executes_true counter (sequence (pushBit counter true) nonzero) zero store result tail
    (1+1+time) nonempty combined
  simpa only [branchUnary,show 1+(1+1+time)=time+3 by omega] using run

end Counting.StackMachine.Routine
