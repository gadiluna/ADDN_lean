import Counting.StackLookupHead
import Counting.StackRoutineBasic

/-! Runtime bit lookup, preserving both the source word and unary index. -/
namespace Counting.StackMachine.Lookup

set_option backward.isDefEq.respectTransparency false

/-- Roles: source, unary index, bit output, presence flag, and three empty
scratch registers. Arbitrary embeddings allow reuse inside larger machines. -/
def preservingLookup (extra : Nat) (w : Fin 7 ↪ Fin (extra+7)) : Routine (extra+5) :=
  Routine.sequence (Routine.ofProgram (ListPrograms.copyProgram (extra+4) (w 0) (w 4) (w 6)))
    (Routine.sequence (Routine.ofProgram (ListPrograms.copyProgram (extra+4) (w 1) (w 5) (w 6)))
      (Routine.sequence (Routine.ofProgram (dropProgram (extra+5) (w 4) (w 5)))
        (Routine.sequence (Routine.ofProgram (headProgram (extra+5) (w 4) (w 2) (w 3)))
          (Routine.clear (w 4)))))

def lookupCost (input index : List Bool) : Nat :=
  5*input.length+2+1+(5*index.length+2+1+(2*index.length+1+1+
    (headCost (input.drop index.length)+1+((input.drop index.length).tail.length+1))))

theorem lookupCost_le (input index : List Bool) :
    lookupCost input index ≤ 6*input.length+7*index.length+13 := by
  have headBound := headCost_le (input.drop index.length)
  simp only [lookupCost,List.length_tail,List.length_drop]
  omega

/-- The lookup has an exact charged run on every word and index, including
out-of-range indices. The status separates a missing bit from a false bit. -/
theorem preservingLookup_executes (extra : Nat) (w : Fin 7 ↪ Fin (extra+7))
    (store : Fin (extra+7) → List Bool)
    (sourceEmpty : store (w 4)=[]) (indexEmpty : store (w 5)=[]) (workEmpty : store (w 6)=[]) :
    Routine.Executes (preservingLookup extra w) store
      (lookupCost (store (w 0)) (store (w 1)))
      (Function.update (Function.update store (w 2)
        ((store (w 0))[(store (w 1)).length]?.toList++store (w 2)))
        (w 3) ((store (w 0))[(store (w 1)).length]?.isSome::store (w 3))) := by
  have distinct (i j : Fin 7) (h : i ≠ j) : w i ≠ w j := fun eq => h (w.injective eq)
  let first := Function.update store (w 4) (store (w 0))
  let second := Function.update first (w 5) (store (w 1))
  let suffix := (store (w 0)).drop (store (w 1)).length
  let dropped := Function.update (Function.update second (w 5) []) (w 4) suffix
  let read := Function.update (Function.update (Function.update dropped (w 4) suffix.tail)
    (w 2) (suffix.head?.toList++store (w 2))) (w 3) (suffix.head?.isSome::store (w 3))
  have copiedSource : Routine.Executes
      (Routine.ofProgram (ListPrograms.copyProgram (extra+4) (w 0) (w 4) (w 6)))
      store (5*(store (w 0)).length+2) first := by
    simpa +instances only [ListPrograms.copyProgram,first,sourceEmpty,List.append_nil] using
      Routine.copy_executes (extra+4) (w 0) (w 4) (w 6)
        (distinct 0 4 (by decide)) (distinct 0 6 (by decide)) (distinct 4 6 (by decide)) store workEmpty
  have firstAt (i : Fin 7) (h : i≠4) : first (w i)=store (w i) := by
    simp only [first,Function.update_of_ne (distinct i 4 h)]
  have copiedIndex : Routine.Executes
      (Routine.ofProgram (ListPrograms.copyProgram (extra+4) (w 1) (w 5) (w 6)))
      first (5*(store (w 1)).length+2) second := by
    have run := Routine.copy_executes (extra+4) (w 1) (w 5) (w 6)
      (distinct 1 5 (by decide)) (distinct 1 6 (by decide)) (distinct 5 6 (by decide)) first
      (by rw [firstAt 6 (by decide),workEmpty])
    simpa +instances only [ListPrograms.copyProgram,firstAt 1 (by decide),firstAt 5 (by decide),
      indexEmpty,List.append_nil,second] using run
  have droppedRun : Routine.Executes (Routine.ofProgram (dropProgram (extra+5) (w 4) (w 5)))
      second (2*(store (w 1)).length+1) dropped := by
    simpa +instances only [dropProgram,second,first,Function.update_self,
      Function.update_of_ne (distinct 4 5 (by decide)),suffix,dropped] using
      drop_executes (extra+5) (w 4) (w 5) (distinct 4 5 (by decide)) second
  have droppedSource : dropped (w 4)=suffix := by simp [dropped]
  have droppedOutput : dropped (w 2)=store (w 2) := by
    simp [dropped,second,first,w.injective.eq_iff]
  have droppedStatus : dropped (w 3)=store (w 3) := by
    simp [dropped,second,first,w.injective.eq_iff]
  have readRun : Routine.Executes (Routine.ofProgram (headProgram (extra+5) (w 4) (w 2) (w 3)))
      dropped (headCost suffix) read := by
    have run := head_executes (extra+5) (w 4) (w 2) (w 3)
      (distinct 4 2 (by decide)) (distinct 4 3 (by decide)) (distinct 2 3 (by decide)) dropped
    simpa +instances only [headProgram,droppedSource,droppedOutput,droppedStatus,read] using run
  have cleared := Routine.clear_executes (registers := extra+5) (w 4) read
  have readSource : read (w 4)=suffix.tail := by simp [read,w.injective.eq_iff]
  rw [readSource] at cleared
  have restored : Function.update read (w 4) [] =
      Function.update (Function.update store (w 2) (suffix.head?.toList++store (w 2)))
        (w 3) (suffix.head?.isSome::store (w 3)) := by
    funext r
    by_cases a : r=w 4
    · subst r; simp [read,sourceEmpty,w.injective.eq_iff]
    · by_cases b : r=w 5
      · subst r; simp [read,dropped,indexEmpty,w.injective.eq_iff]
      · by_cases c : r=w 2
        · subst r; simp [read,w.injective.eq_iff]
        · by_cases d : r=w 3
          · subst r; simp [read,w.injective.eq_iff]
          · simp [read,dropped,second,first,a,b,c,d]
  rw [restored] at cleared
  have combined := copiedSource.sequence (copiedIndex.sequence (droppedRun.sequence (readRun.sequence cleared)))
  simpa only [preservingLookup,lookupCost,suffix,List.head?_drop] using combined

end Counting.StackMachine.Lookup
