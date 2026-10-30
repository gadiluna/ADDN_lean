import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

abbrev discardBit {registers : Nat} (target : Fin (registers+2)) : Routine registers :=
  ⟨1,fun control => if control = 0 then .pop target 1 1 1 else .halt⟩

theorem discardBit_executes (target : Fin (registers+2)) (store : Store registers) :
    Executes (discardBit target) store 1 (Function.update store target (store target).tail) := by
  refine ⟨⟨1,Function.update store target (store target).tail⟩,?_,?_,rfl⟩
  · cases content : store target with
    | nil =>
        have same : Function.update store target [] = store := by rw [← content,Function.update_eq_self]
        simp [Machine.run,step,discardBit,content,same]
    | cons bit rest => cases bit <;> simp [Machine.run,step,discardBit,content]
  · simp [step,discardBit]

/-- Remove a fixed number of leading bits. The number is a compile-time
constant, and every pop and every connecting jump contributes to the cost. -/
def discard (target : Fin (registers+2)) : Nat → Routine registers
  | 0 => skip registers
  | count+1 => sequence (discard target count) (discardBit target)

theorem discard_executes (target : Fin (registers+2)) (count : Nat) (store : Store registers) :
    Executes (discard target count) store (2*count) (Function.update store target ((store target).drop count)) := by
  induction count with
  | zero => simpa only [discard,Nat.mul_zero,List.drop_zero,Function.update_eq_self] using skip_executes store
  | succ count ih =>
      have combined := ih.sequence (discardBit_executes target (Function.update store target ((store target).drop count)))
      simpa only [discard,Function.update_self,Function.update_idem,List.tail_drop,
        show 2*(count+1)=2*count+1+1 by omega] using combined

end Counting.StackMachine.Routine
