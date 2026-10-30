import Counting.StackEncodingRoutineInterfaces

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

theorem frameResult_updates (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (store : Fin (extra+3) → List Bool) (empty : store temporary=[]) :
    frameResult extra source target temporary store =
      Function.update (Function.update store source []) target (Encoding.frame (store source)++store target) := by
  funext r
  by_cases a : r=source
  · subst r; simp [frameResult,st]
  · by_cases b : r=target
    · subst r; simp [frameResult,Ne.symm st]
    · by_cases c : r=temporary
      · subst r; simp [frameResult,Ne.symm sw,Ne.symm tw,empty]
      · simp [frameResult,a,b,c]

theorem frame_executes_updates (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (store : Fin (extra+3) → List Bool) (empty : store temporary=[]) :
    Routine.Executes (frameRoutine extra source target temporary) store (5*(store source).length+4)
      (Function.update (Function.update store source []) target (Encoding.frame (store source)++store target)) := by
  rw [← frameResult_updates extra source target temporary st sw tw store empty]
  exact frame_executes extra source target temporary st sw tw store empty

end Counting.StackMachine.EncodingPrograms
