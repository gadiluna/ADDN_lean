import Counting.StackRoutineLists

namespace Counting.StackMachine.RealizabilityCheck
open Routine

def statusOutput : Routine 98 := ofProgram (ListPrograms.reverseProgram 98 85 1)

theorem statusOutput_executes (store : Store 98) (answer : Bool)
    (empty : store 1=[]) (status : store 85=[answer]) :
    ∃ result : Store 98, Executes statusOutput store 3 result ∧ result 1=[answer] := by
  have run := reverse_executes 98 (85:Fin 100) 1 (by decide) store
  rw [status,empty] at run
  simpa only [List.length_singleton,List.reverse_singleton,List.append_nil] using
    (show ∃ result,Executes statusOutput store (2*1+1) result ∧ result 1=[answer] from
      ⟨_,run,by simp⟩)

end Counting.StackMachine.RealizabilityCheck
