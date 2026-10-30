import Counting.ExternalMatchingVariableLoop

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

abbrev VariableWorkspace (extra : Nat) := RowWorkspace extra

def variablePrepare (extra : Nat) (w : VariableWorkspace extra) : Routine (extra+13) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+12) (w 0) (w 14) (w 9)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+12) (w 0) (w 1) (w 9)))
      (sequence (pushBit (w 1) true) (ofProgram (ListPrograms.copyProgram (extra+12) (w 13) (w 12) (w 9)))))

def variablePrepared (extra : Nat) (w : VariableWorkspace extra) (store : Fin (extra+15) → List Bool) :=
  Function.update (Function.update (Function.update store (w 14) (store (w 0)))
    (w 1) (true::store (w 0))) (w 12) (store (w 13))

theorem variablePrepare_executes (extra : Nat) (w : VariableWorkspace extra) (store : Fin (extra+15) → List Bool)
    (empty1 : store (w 1)=[]) (empty9 : store (w 9)=[]) (empty12 : store (w 12)=[]) (empty14 : store (w 14)=[]) :
    Executes (variablePrepare extra w) store (10*(store (w 0)).length+5*(store (w 13)).length+10)
      (variablePrepared extra w store) := by
  let saved := Function.update store (w 14) (store (w 0))
  have save : Executes (ofProgram (ListPrograms.copyProgram (extra+12) (w 0) (w 14) (w 9))) store
      (5*(store (w 0)).length+2) saved := by
    simpa +instances only [saved,empty14,List.append_nil,ListPrograms.copyProgram] using
      copy_executes (extra+12) (w 0) (w 14) (w 9) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store empty9
  let duplicated := Function.update saved (w 1) (store (w 0))
  have duplicate : Executes (ofProgram (ListPrograms.copyProgram (extra+12) (w 0) (w 1) (w 9))) saved
      (5*(store (w 0)).length+2) duplicated := by
    simpa +instances [saved,duplicated,w.injective.eq_iff,empty1,ListPrograms.copyProgram] using
      copy_executes (extra+12) (w 0) (w 1) (w 9) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) saved (by simp [saved,w.injective.eq_iff,empty9])
  let incremented := Function.update saved (w 1) (true::store (w 0))
  have increment : Executes (pushBit (w 1) true) duplicated 1 incremented := by
    simpa only [duplicated,incremented,Function.update_self,Function.update_idem] using pushBit_executes (w 1) true duplicated
  have copy := copy_executes (extra+12) (w 13) (w 12) (w 9) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) incremented
    (by simp [incremented,saved,w.injective.eq_iff,empty9])
  have copied : Executes (ofProgram (ListPrograms.copyProgram (extra+12) (w 13) (w 12) (w 9))) incremented
      (5*(store (w 13)).length+2) (variablePrepared extra w store) := by
    simpa +instances [variablePrepared,incremented,saved,w.injective.eq_iff,empty12,ListPrograms.copyProgram] using copy
  have composed := save.sequence (duplicate.sequence (increment.sequence copied))
  convert composed using 1 <;> first | rfl | omega

/-- Replace the successor counter by the saved first vertex, closing the
variable cycle. The first counter and both data streams are preserved. -/
def variableWrap (extra : Nat) (w : VariableWorkspace extra) : Routine (extra+13) :=
  sequence (clear (w 1)) (ofProgram (ListPrograms.copyProgram (extra+12) (w 14) (w 1) (w 9)))

theorem variableWrap_executes (extra : Nat) (w : VariableWorkspace extra) (store : Fin (extra+15) → List Bool)
    (work : store (w 9)=[]) :
    Executes (variableWrap extra w) store ((store (w 1)).length+5*(store (w 14)).length+4)
      (Function.update store (w 1) (store (w 14))) := by
  have clean := clear_executes (w 1) store
  let cleaned := Function.update store (w 1) []
  have copied := copy_executes (extra+12) (w 14) (w 1) (w 9) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) cleaned
    (by simp [cleaned,w.injective.eq_iff,work])
  have copyAs : Executes (ofProgram (ListPrograms.copyProgram (extra+12) (w 14) (w 1) (w 9))) cleaned
      (5*(store (w 14)).length+2) (Function.update store (w 1) (store (w 14))) := by
    simpa +instances [cleaned,w.injective.eq_iff,ListPrograms.copyProgram] using copied
  have composed := clean.sequence copyAs
  convert composed using 1 <;> first | rfl | omega

end Counting.External.MatchingMachine
