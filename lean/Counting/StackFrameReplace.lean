import Counting.StackFrameReplaceSpec
import Counting.StackRoutineLists

namespace Counting.StackMachine.FieldAccess
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Source, unary index, encoded replacement, empty reversed-prefix scratch,
and empty copy scratch. Only source and index change at return. -/
def replaceRoutine (extra : Nat) (w : Fin 5 ↪ Fin (extra+5)) : Routine (extra+3) :=
  sequence (forEach (w 1) (ofProgram (moveProgram (extra+3) (w 0) (w 3))))
    (sequence (ofProgram (skipProgram (extra+3) (w 0)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+2) (w 2) (w 0) (w 4)))
        (ofProgram (ListPrograms.reverseProgram (extra+3) (w 3) (w 0)))))

def replaceCost (input index replacement : List Bool) : Nat :=
  moveManyCost index.length input+1+(skipCost (skipMany index.length input)+1+
    (5*replacement.length+2+1+(2*(frontMany index.length input).length+1)))

theorem replaceCost_le (input index replacement : List Bool) :
    replaceCost input index replacement ≤ 5*input.length+3*index.length+5*replacement.length+8 := by
  have moved := moveManyCost_le index.length input
  have skipped := skipCost_le (skipMany index.length input)
  have remaining := skipMany_length index.length input
  have copied := frontMany_length index.length input
  simp only [replaceCost]
  omega

theorem replace_executes (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) (prefixEmpty : store (w 3)=[]) (workEmpty : store (w 4)=[]) :
    Executes (replaceRoutine extra w) store (replaceCost (store (w 0)) (store (w 1)) (store (w 2)))
      (Function.update (Function.update store (w 1) []) (w 0)
        (replaceFieldWord (store (w 0)) (store (w 1)).length (store (w 2)))) := by
  have distinct (i j : Fin 5) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  let before := frontMany (store (w 1)).length (store (w 0))
  let after := skipMany (store (w 1)).length (store (w 0))
  let moved := Function.update (Function.update (Function.update store (w 1) []) (w 0) after)
    (w 3) before.reverse
  let removed := Function.update moved (w 0) (skipRest after)
  let inserted := Function.update removed (w 0) (store (w 2)++skipRest after)
  have moving : Executes (forEach (w 1) (ofProgram (moveProgram (extra+3) (w 0) (w 3))))
      store (moveManyCost (store (w 1)).length (store (w 0))) moved := by
    simpa +instances only [moveProgram,prefixEmpty,List.append_nil,before,after,moved] using
      moveMany_executes (extra+3) (w 0) (w 1) (w 3) (distinct 0 1 (by decide))
        (distinct 0 3 (by decide)) (distinct 3 1 (by decide)) store
  have movedSource : moved (w 0)=after := by simp [moved,w.injective.eq_iff]
  have removing : Executes (ofProgram (skipProgram (extra+3) (w 0))) moved (skipCost after) removed := by
    simpa +instances only [skipProgram,movedSource,removed] using skip_executes (extra+3) (w 0) moved
  have removedSource : removed (w 0)=skipRest after := by simp [removed]
  have removedReplacement : removed (w 2)=store (w 2) := by simp [removed,moved,w.injective.eq_iff]
  have removedWork : removed (w 4)=[] := by simp [removed,moved,w.injective.eq_iff,workEmpty]
  have inserting : Executes (ofProgram (ListPrograms.copyProgram (extra+2) (w 2) (w 0) (w 4)))
      removed (5*(store (w 2)).length+2) inserted := by
    simpa +instances only [ListPrograms.copyProgram,removedSource,removedReplacement,inserted] using
      copy_executes (extra+2) (w 2) (w 0) (w 4) (distinct 2 0 (by decide))
        (distinct 2 4 (by decide)) (distinct 0 4 (by decide)) removed removedWork
  have insertedPrefix : inserted (w 3)=before.reverse := by simp [inserted,removed,moved,w.injective.eq_iff]
  have insertedSource : inserted (w 0)=store (w 2)++skipRest after := by simp [inserted]
  have restoring := reverse_executes (extra+3) (w 3) (w 0) (distinct 3 0 (by decide)) inserted
  simp +instances only [ListPrograms.reverseProgram] at restoring
  rw [insertedPrefix,insertedSource,List.length_reverse,List.reverse_reverse] at restoring
  have final : Function.update (Function.update inserted (w 3) []) (w 0)
      (before++(store (w 2)++skipRest after)) =
      Function.update (Function.update store (w 1) []) (w 0)
        (replaceFieldWord (store (w 0)) (store (w 1)).length (store (w 2))) := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [replaceFieldWord,before,after,List.append_assoc]
    · by_cases b : r=w 3
      · subst r; simp [w.injective.eq_iff,prefixEmpty]
      · simp [Function.update_of_ne a,Function.update_of_ne b,inserted,removed,moved]
  rw [final] at restoring
  exact moving.sequence (removing.sequence (inserting.sequence restoring))

end Counting.StackMachine.FieldAccess
