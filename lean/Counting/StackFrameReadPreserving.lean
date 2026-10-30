import Counting.StackFrameRead
import Counting.StackRoutineLists
import Counting.StackRoutineBasic

namespace Counting.StackMachine.FieldAccess
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Source, unary index, payload, flag, and four empty scratch registers. -/
def readerRoles (w : Fin 8 ↪ Fin (extra+8)) : Fin 5 ↪ Fin (extra+8) where
  toFun i := w (![4,5,2,6,3] i)
  inj' := fun _ _ h => (by decide : Function.Injective (fun i : Fin 5 => (![4,5,2,6,3] i : Fin 8)))
    (w.injective h)

def preservingRead (extra : Nat) (w : Fin 8 ↪ Fin (extra+8)) : Routine (extra+6) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 0) (w 4) (w 7)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 5) (w 7)))
      (sequence (readField (extra+3) (readerRoles w)) (clear (w 4))))

theorem preservingRead_executes (extra : Nat) (w : Fin 8 ↪ Fin (extra+8))
    (store : Fin (extra+8) → List Bool)
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) :
    ∃ time ≤ 10*(store (w 0)).length+8*(store (w 1)).length+14,
      Executes (preservingRead extra w) store time
        (Function.update (Function.update store (w 2)
          ((selectPayload (store (w 0)) (store (w 1)).length).getD []++store (w 2)))
          (w 3) ((selectPayload (store (w 0)) (store (w 1)).length).isSome::store (w 3))) := by
  have distinct (i j : Fin 8) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  let first := Function.update store (w 4) (store (w 0))
  let second := Function.update first (w 5) (store (w 1))
  have firstAt (i : Fin 8) (h : i≠4) : first (w i)=store (w i) := by
    simp [first,distinct i 4 h]
  have secondAt (i : Fin 8) (h4 : i≠4) (h5 : i≠5) : second (w i)=store (w i) := by
    simp [second,distinct i 5 h5,firstAt i h4]
  have firstCopy : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 0) (w 4) (w 7)))
      store (5*(store (w 0)).length+2) first := by
    simpa +instances only [ListPrograms.copyProgram,first,e4,List.append_nil] using
      copy_executes (extra+5) (w 0) (w 4) (w 7) (distinct 0 4 (by decide))
        (distinct 0 7 (by decide)) (distinct 4 7 (by decide)) store e7
  have secondCopy : Executes (ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 5) (w 7)))
      first (5*(store (w 1)).length+2) second := by
    have run := copy_executes (extra+5) (w 1) (w 5) (w 7) (distinct 1 5 (by decide))
      (distinct 1 7 (by decide)) (distinct 5 7 (by decide)) first (by rw [firstAt 7 (by decide),e7])
    simpa +instances only [ListPrograms.copyProgram,firstAt 1 (by decide),firstAt 5 (by decide),e5,
      List.append_nil,second] using run
  let result := readResult (extra+3) (readerRoles w) second
  have readerInput : second (readerRoles w 0)=store (w 0) := by simp [readerRoles,second,first,w.injective.eq_iff]
  have readerIndex : second (readerRoles w 1)=store (w 1) := by simp [readerRoles,second]
  have readerOutput : second (readerRoles w 2)=store (w 2) := by exact secondAt 2 (by decide) (by decide)
  have readerFlag : second (readerRoles w 4)=store (w 3) := by exact secondAt 3 (by decide) (by decide)
  have readerWork : second (readerRoles w 3)=[] := by rw [show readerRoles w 3=w 6 from rfl,secondAt 6 (by decide) (by decide),e6]
  obtain ⟨readTime,readBound,readRun⟩ := readField_executes (extra+3) (readerRoles w) second readerWork
  rw [readerInput,readerIndex] at readBound
  have sourceBound := readResult_source_length (extra+3) (readerRoles w) second
  rw [readerInput] at sourceBound
  change (result (w 4)).length ≤ (store (w 0)).length at sourceBound
  have payload := readResult_payload (extra+3) (readerRoles w) second
  rw [readerInput,readerIndex,readerOutput] at payload
  have flag := readResult_status (extra+3) (readerRoles w) second
  rw [readerInput,readerIndex,readerFlag] at flag
  have counter := readResult_counter (extra+3) (readerRoles w) second
  have scratch := readResult_scratch (extra+3) (readerRoles w) second
  change result (w 2)=_ at payload
  change result (w 3)=_ at flag
  change result (w 5)=[] at counter
  change result (w 6)=[] at scratch
  have cleared := clear_executes (registers := extra+6) (w 4) result
  have restored : Function.update result (w 4) [] =
      Function.update (Function.update store (w 2)
        ((selectPayload (store (w 0)) (store (w 1)).length).getD []++store (w 2)))
        (w 3) ((selectPayload (store (w 0)) (store (w 1)).length).isSome::store (w 3)) := by
    funext r
    by_cases a : r=w 4
    · subst r; simp [e4,w.injective.eq_iff]
    · by_cases b : r=w 2
      · subst r; simp [payload,w.injective.eq_iff]
      · by_cases c : r=w 3
        · subst r; simp [flag,w.injective.eq_iff]
        · by_cases d : r=w 5
          · subst r; simp [counter,e5,w.injective.eq_iff]
          · by_cases e : r=w 6
            · subst r; simp [scratch,e6,w.injective.eq_iff]
            · have unchanged := readResult_other (extra+3) (readerRoles w) second r (by
                intro i
                fin_cases i <;> assumption)
              change result r=second r at unchanged
              simp [a,b,c,d,unchanged,second,first]
  rw [restored] at cleared
  refine ⟨_,?_,firstCopy.sequence (secondCopy.sequence (readRun.sequence cleared))⟩
  omega

end Counting.StackMachine.FieldAccess
