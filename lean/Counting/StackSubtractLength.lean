import Counting.StackLookupDrop

namespace Counting.StackMachine.Routine

/-- Drop the source length from the target, preserving the source. Counter
and temporary storage are restored by real copy/drop programs. -/
def subtractLength (extra : Nat) (source target counter work : Fin (extra+4)) : Routine (extra+2) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+1) source counter work))
    (ofProgram (Lookup.dropProgram (extra+2) target counter))

theorem subtractLength_executes (extra : Nat) (source target counter work : Fin (extra+4))
    (sc : source ≠ counter) (sw : source ≠ work) (cw : counter ≠ work) (tc : target ≠ counter)
    (store : Fin (extra+4) → List Bool) (counterEmpty : store counter=[]) (workEmpty : store work=[]) :
    Executes (subtractLength extra source target counter work) store (7*(store source).length+4)
      (Function.update store target ((store target).drop (store source).length)) := by
  let copied := Function.update store counter (store source)
  have copiedRun : Executes (ofProgram (ListPrograms.copyProgram (extra+1) source counter work)) store
      (5*(store source).length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,counterEmpty,List.append_nil,copied] using
      copy_executes (extra+1) source counter work sc sw cw store workEmpty
  have dropped := Lookup.drop_executes (extra+2) target counter tc copied
  have restored : Function.update copied counter [] = store := by
    simp only [copied,Function.update_idem,← counterEmpty,Function.update_eq_self]
  have counterValue : copied counter=store source := by simp [copied]
  have targetValue : copied target=store target := by simp [copied,tc]
  have droppedRun : Executes (ofProgram (Lookup.dropProgram (extra+2) target counter)) copied
      (2*(store source).length+1) (Function.update store target ((store target).drop (store source).length)) := by
    simpa +instances only [Lookup.dropProgram,restored,counterValue,targetValue] using dropped
  have combined := copiedRun.sequence droppedRun
  simpa +instances only [subtractLength,ListPrograms.copyProgram,Lookup.dropProgram,
    show 5*(store source).length+2+1+(2*(store source).length+1)=7*(store source).length+4 by omega] using combined

end Counting.StackMachine.Routine
