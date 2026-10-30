import Counting.StackEmitBinary
import Counting.DagAddCountSpec
import Counting.StackRoutineBasic

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Roles: source stream, insertion index, increment, reverse output,
pending flag, output length, current index/count, followed by scratch. -/
abbrev AddWorkspace (extra : Nat) := Fin 20 ↪ Fin (extra+20)

def AddWorkspace.currentEmitter (w : AddWorkspace extra) : BinaryPairEmitterWorkspace (extra+15) :=
  (⟨![6,7,3,15,16],by decide⟩ : Fin 5 ↪ Fin 20).trans w

def AddWorkspace.newEmitter (w : AddWorkspace extra) : BinaryPairEmitterWorkspace (extra+15) :=
  (⟨![8,9,3,15,16],by decide⟩ : Fin 5 ↪ Fin 20).trans w

def emitCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (emitBinaryPair (extra+15) w.currentEmitter) (pushBit (w 5) true)

theorem emitCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (buffer : store (w 15)=[]) (scratch : store (w 16)=[]) :
    Executes (emitCurrent extra w) store (9*((store (w 6)).length+(store (w 7)).length)+19)
      (Function.update (Function.update (Function.update (Function.update store
        (w 6) []) (w 7) []) (w 3)
        ((Encoding.frame (store (w 6))++Encoding.frame (store (w 7))).reverse++store (w 3)))
        (w 5) (true::store (w 5))) := by
  have emitting:=emitBinaryPair_executes (extra+15) w.currentEmitter store buffer scratch
  let emitted:=Function.update (Function.update (Function.update store (w 6) []) (w 7) []) (w 3)
    ((Encoding.frame (store (w 6))++Encoding.frame (store (w 7))).reverse++store (w 3))
  change Executes (emitBinaryPair (extra+15) w.currentEmitter) store
    (9*((store (w 6)).length+(store (w 7)).length)+17) emitted at emitting
  have pushing:=pushBit_executes (w 5) true emitted
  have counter : emitted (w 5)=store (w 5) := by simp [emitted,w.injective.eq_iff]
  rw [counter] at pushing
  simpa only [emitCurrent,show 9*((store (w 6)).length+(store (w 7)).length)+17+1+1=
    9*((store (w 6)).length+(store (w 7)).length)+19 by omega] using emitting.sequence pushing

def emitNew (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+17) (w 1) (w 8) (w 10)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+17) (w 2) (w 9) (w 10)))
      (sequence (emitBinaryPair (extra+15) w.newEmitter) (pushBit (w 5) true)))

theorem emitNew_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (empty : ∀ i∈([8,9,10,15,16]:List (Fin 20)),store (w i)=[]) :
    Executes (emitNew extra w) store (14*((store (w 1)).length+(store (w 2)).length)+25)
      (Function.update (Function.update store (w 3)
        ((Encoding.frame (store (w 1))++Encoding.frame (store (w 2))).reverse++store (w 3)))
        (w 5) (true::store (w 5))) := by
  have ne (i j : Fin 20) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  have first:=copy_executes (extra+17) (w 1) (w 8) (w 10)
    (ne 1 8 (by decide)) (ne 1 10 (by decide)) (ne 8 10 (by decide)) store (empty 10 (by simp))
  rw [empty 8 (by simp),List.append_nil] at first
  let one:=Function.update store (w 8) (store (w 1))
  have second:=copy_executes (extra+17) (w 2) (w 9) (w 10)
    (ne 2 9 (by decide)) (ne 2 10 (by decide)) (ne 9 10 (by decide)) one
    (by simp [one,w.injective.eq_iff,empty])
  have sourceAt : one (w 2)=store (w 2) := by simp [one,w.injective.eq_iff]
  have targetAt : one (w 9)=[] := by simp [one,w.injective.eq_iff,empty]
  rw [sourceAt,targetAt,List.append_nil] at second
  let copied:=Function.update one (w 9) (store (w 2))
  have emitting:=emitBinaryPair_executes (extra+15) w.newEmitter copied
    (by simp [AddWorkspace.newEmitter,copied,one,w.injective.eq_iff,empty])
    (by simp [AddWorkspace.newEmitter,copied,one,w.injective.eq_iff,empty])
  have current : copied (w.newEmitter 0)=store (w 1) := by simp [AddWorkspace.newEmitter,copied,one,w.injective.eq_iff]
  have increment : copied (w.newEmitter 1)=store (w 2) := by simp [AddWorkspace.newEmitter,copied]
  rw [current,increment] at emitting
  let emitted:=Function.update store (w 3)
    ((Encoding.frame (store (w 1))++Encoding.frame (store (w 2))).reverse++store (w 3))
  have final : Function.update (Function.update (Function.update copied
      (w.newEmitter 0) []) (w.newEmitter 1) []) (w.newEmitter 2)
      ((Encoding.frame (store (w 1))++Encoding.frame (store (w 2))).reverse++copied (w.newEmitter 2))=emitted := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [AddWorkspace.newEmitter,copied,one,emitted,w.injective.eq_iff]
    · by_cases b : r=w 8
      · subst r;simp [AddWorkspace.newEmitter,emitted,w.injective.eq_iff,empty]
      · by_cases c : r=w 9
        · subst r;simp [AddWorkspace.newEmitter,emitted,w.injective.eq_iff,empty]
        · simp [AddWorkspace.newEmitter,copied,one,emitted,a,b,c]
  rw [final] at emitting
  have pushing:=pushBit_executes (w 5) true emitted
  have counter : emitted (w 5)=store (w 5) := by simp [emitted,w.injective.eq_iff]
  rw [counter] at pushing
  have composed:=first.sequence (second.sequence (emitting.sequence pushing))
  simpa only [emitNew,show 5*(store (w 1)).length+2+1+(5*(store (w 2)).length+2+1+
    (9*((store (w 1)).length+(store (w 2)).length)+17+1+1))=
      14*((store (w 1)).length+(store (w 2)).length)+25 by omega] using composed

end Counting.StackMachine.DagUpdate
