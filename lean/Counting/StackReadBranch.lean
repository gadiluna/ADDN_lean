import Counting.StackUnaryBranch

namespace Counting.StackMachine.Routine
open EncodingPrograms

/-- Read a Boolean condition while restoring its bit. The restoration and
control-transfer instructions are counted, and no branch inspects an oracle. -/
def branchRead {registers : Nat} (flag : Fin (registers+2)) (yes no : Routine registers) : Routine registers :=
  branchRoutine flag (sequence (pushBit flag true) yes) (sequence (pushBit flag false) no)

theorem branchRead_executes {registers : Nat} (flag : Fin (registers+2)) (yes no : Routine registers)
    (bit : Bool) (tail : List Bool) (store result : Store registers) (time : Nat)
    (condition : store flag=bit::tail)
    (executed : Executes (if bit then yes else no) store time result) :
    Executes (branchRead flag yes no) store (time+3) result := by
  have restored := pushBit_executes flag bit (Function.update store flag tail)
  have equal : Function.update (Function.update store flag tail) flag
      (bit::Function.update store flag tail flag)=store := by
    rw [Function.update_self,Function.update_idem,← condition,Function.update_eq_self]
  rw [equal] at restored
  cases bit
  · have combined := restored.sequence executed
    have run := branch_executes_false flag (sequence (pushBit flag true) yes) (sequence (pushBit flag false) no)
      store result tail (1+1+time) condition combined
    simpa only [branchRead,show 1+(1+1+time)=time+3 by omega] using run
  · have combined := restored.sequence executed
    have run := branch_executes_true flag (sequence (pushBit flag true) yes) (sequence (pushBit flag false) no)
      store result tail (1+1+time) condition combined
    simpa only [branchRead,show 1+(1+1+time)=time+3 by omega] using run

end Counting.StackMachine.Routine
