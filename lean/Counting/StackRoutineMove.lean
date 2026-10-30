import Counting.StackRoutineLists
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

/-- Preserve order while consuming the source. The destination's existing
suffix is retained, and the temporary register is restored empty. -/
def move (extra : Nat) (source target scratch : Fin (extra+3)) : Routine (extra+1) :=
  sequence (ofProgram (ListPrograms.copyProgram extra source target scratch)) (clear source)

theorem move_executes (extra : Nat) (source target scratch : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ scratch) (tw : target ≠ scratch)
    (store : Fin (extra+3) → List Bool) (empty : store scratch = []) :
    Executes (move extra source target scratch) store (6*(store source).length+4)
      (Function.update (Function.update store target (store source++store target)) source []) := by
  have copied := copy_executes extra source target scratch st sw tw store empty
  have cleared := clear_executes (registers := extra+1) source
    (Function.update store target (store source++store target))
  rw [Function.update_of_ne st] at cleared
  have composed := copied.sequence cleared
  simp only [show (5*(store source).length+2)+1+((store source).length+1) =
    6*(store source).length+4 by omega] at composed
  exact composed

end Counting.StackMachine.Routine
