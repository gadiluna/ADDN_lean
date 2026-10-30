import Counting.ExternalInitialCounters
import Counting.StackRoutineUnary

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Form the absolute first-cell index without consuming the input header or counters. -/
def initialBinaryBase (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+21) (w 1) (w 6) (w 20)))
    (sequence (ofProgram (Unary.lengthProgram (extra+21) (w 2) (w 6) (w 20)))
      (ofProgram (ListPrograms.copyProgram (extra+21) (w 0) (w 6) (w 20))))

theorem initialBinaryBase_executes (extra : Nat) (w : InitialWorkspace extra) (place offset : Nat)
    (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (baseEmpty : store (w 6)=[]) (workEmpty : store (w 20)=[]) :
    Executes (initialBinaryBase extra w) store (5*offset+5*(store (w 2)).length+5*place+8)
      (Function.update store (w 6) (List.replicate (offset+(store (w 2)).length+place) true)) := by
  let first := Function.update store (w 6) (List.replicate offset true)
  let second := Function.update store (w 6) (List.replicate (offset+(store (w 2)).length) true)
  have copied : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 1) (w 6) (w 20))) store
      (5*offset+2) first := by
    simpa +instances only [ListPrograms.copyProgram,offsetValue,baseEmpty,List.append_nil,List.length_replicate,first] using
      copy_executes (extra+21) (w 1) (w 6) (w 20)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store workEmpty
  have measured : Executes (ofProgram (Unary.lengthProgram (extra+21) (w 2) (w 6) (w 20))) first
      (5*(store (w 2)).length+2) second := by
    have run := length_executes (extra+21) (w 2) (w 6) (w 20)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) first
      (by simp [first,w.injective.eq_iff,workEmpty])
    simpa +instances [Unary.lengthProgram,first,second,w.injective.eq_iff,← List.replicate_add,Nat.add_comm] using run
  have added : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 0) (w 6) (w 20))) second
      (5*place+2) (Function.update store (w 6) (List.replicate (offset+(store (w 2)).length+place) true)) := by
    have run := copy_executes (extra+21) (w 0) (w 6) (w 20)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) second
      (by simp [second,w.injective.eq_iff,workEmpty])
    simpa +instances [ListPrograms.copyProgram,second,w.injective.eq_iff,placeValue,← List.replicate_add,Nat.add_comm] using run
  have combined := copied.sequence (measured.sequence added)
  simpa +instances only [initialBinaryBase,ListPrograms.copyProgram,Unary.lengthProgram,
    show 5*offset+2+1+(5*(store (w 2)).length+2+1+(5*place+2))=5*offset+5*(store (w 2)).length+5*place+8 by omega] using combined

end Counting.External.CookLevin.StackGenerator
