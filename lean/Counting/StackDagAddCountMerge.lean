import Counting.StackDagAddCountEmit
import Counting.StackRealizabilityAccumulate
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false

def AddWorkspace.accumulator (w : AddWorkspace extra) : Fin 4 ↪ Fin (extra+20) :=
  (⟨![7,12,13,14],by decide⟩ : Fin 4 ↪ Fin 20).trans w

def mergeCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+17) (w 2) (w 12) (w 10)))
    (RealizabilityCheck.accumulateAt w.accumulator)

/-- Add the compact binary increment to the current compact count. The
query increment and every unrelated register are preserved. -/
theorem mergeCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (empty : ∀ i∈([10,12,13,14]:List (Fin 20)),store (w i)=[]) :
    ∃ time ≤ 16*((store (w 7)).length+(store (w 2)).length)+23,
      Executes (mergeCurrent extra w) store time
        (Function.update store (w 7)
          (Encoding.value (store (w 7))+Encoding.value (store (w 2))).bits) := by
  have copy:=copy_executes (extra+17) (w 2) (w 12) (w 10)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    store (empty 10 (by simp))
  rw [empty 12 (by simp),List.append_nil] at copy
  let copied:=Function.update store (w 12) (store (w 2))
  obtain ⟨time,bound,adding⟩:=RealizabilityCheck.accumulateAt_executes w.accumulator copied
    (by simp [AddWorkspace.accumulator,copied,w.injective.eq_iff,empty])
    (by simp [AddWorkspace.accumulator,copied,w.injective.eq_iff,empty])
  have firstAt : copied (w.accumulator 0)=store (w 7) := by simp [AddWorkspace.accumulator,copied,w.injective.eq_iff]
  have secondAt : copied (w.accumulator 1)=store (w 2) := by simp [AddWorkspace.accumulator,copied]
  rw [firstAt,secondAt] at bound adding
  have final : Function.update (Function.update copied (w.accumulator 0)
      (Encoding.value (store (w 7))+Encoding.value (store (w 2))).bits) (w.accumulator 1) []=
      Function.update store (w 7) (Encoding.value (store (w 7))+Encoding.value (store (w 2))).bits := by
    funext r
    by_cases a : r=w 12
    · subst r;simp [AddWorkspace.accumulator,w.injective.eq_iff,empty]
    · simp [AddWorkspace.accumulator,copied,Function.update_apply,a]
  rw [final] at adding
  exact ⟨_,by omega,copy.sequence adding⟩

def finishPending (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (discardBit (w 4)) (pushBit (w 4) false)

theorem finishPending_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (pending : Bool) (tail : List Bool) (flag : store (w 4)=pending::tail) :
    Executes (finishPending extra w) store 3 (Function.update store (w 4) (false::tail)) := by
  have popping:=discardBit_executes (w 4) store
  rw [flag,List.tail_cons] at popping
  have pushing:=pushBit_executes (w 4) false (Function.update store (w 4) tail)
  simp only [Function.update_self,Function.update_idem] at pushing
  exact popping.sequence pushing

end Counting.StackMachine.DagUpdate
