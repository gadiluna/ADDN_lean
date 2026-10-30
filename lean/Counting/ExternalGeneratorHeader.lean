import Counting.ExternalGeneratorWorkspace
import Counting.StackEncodingFrame

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms

/-- Preserve the input while computing its self-delimiting header by real
copy, reversal, and framing instructions. -/
def inputHeaderRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 28) (w 30) (w 31)))
    (frameRoutine (extra+29) (w 30) (w 3) (w 21))

theorem inputHeaderRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (store : Fin (extra+32) → List Bool)
    (headerEmpty : store (w 3)=[]) (copyEmpty : store (w 30)=[]) (frameEmpty : store (w 21)=[]) (workEmpty : store (w 31)=[]) :
    Executes (inputHeaderRoutine extra w) store (10*(store (w 28)).length+7)
      (Function.update store (w 3) (Encoding.frame (store (w 28)))) := by
  let copied := Function.update store (w 30) (store (w 28))
  have first : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 28) (w 30) (w 31))) store
      (5*(store (w 28)).length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,copied,copyEmpty,List.append_nil] using
      copy_executes (extra+29) (w 28) (w 30) (w 31)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store workEmpty
  have framed := frame_executes (extra+29) (w 30) (w 3) (w 21)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) copied
    (by simp [copied,w.injective.eq_iff,frameEmpty])
  have result : frameResult (extra+29) (w 30) (w 3) (w 21) copied=
      Function.update store (w 3) (Encoding.frame (store (w 28))) := by
    funext r
    by_cases a : r=w 30
    · subst r; simp [frameResult,w.injective.eq_iff,copyEmpty]
    · by_cases b : r=w 3
      · subst r; simp [frameResult,copied,w.injective.eq_iff,headerEmpty]
      · by_cases c : r=w 21
        · subst r; simp [frameResult,w.injective.eq_iff,frameEmpty]
        · simp [frameResult,copied,a,b,c]
  rw [result] at framed
  have combined := first.sequence framed
  simpa +instances only [inputHeaderRoutine,ListPrograms.copyProgram,copied,Function.update_self,
    show 5*(store (w 28)).length+2+1+(5*(store (w 28)).length+4)=10*(store (w 28)).length+7 by omega] using combined

end Counting.External.CookLevin.StackGenerator
