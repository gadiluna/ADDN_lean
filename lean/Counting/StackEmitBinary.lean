import Counting.StackEncodingFrame
import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine
open EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev BinaryEmitterWorkspace (extra : Nat) := Fin 4 ↪ Fin (extra+4)

/-- Consume an arbitrary binary payload and prepend its reversed frame to
the output stream. Buffer and scratch are restored; no numeric expansion. -/
def emitBinary (extra : Nat) (w : BinaryEmitterWorkspace extra) : Routine (extra+2) :=
  sequence (frameRoutine (extra+1) (w 0) (w 2) (w 3))
    (ofProgram (ListPrograms.reverseProgram (extra+2) (w 2) (w 1)))

theorem emitBinary_executes (extra : Nat) (w : BinaryEmitterWorkspace extra)
    (store : Store (extra+2)) (buffer : store (w 2)=[]) (scratch : store (w 3)=[]) :
    Executes (emitBinary extra w) store (9*(store (w 0)).length+8)
      (Function.update (Function.update store (w 0) []) (w 1)
        ((Encoding.frame (store (w 0))).reverse++store (w 1))) := by
  have ne (i j : Fin 4) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  have framing:=frame_executes (extra+1) (w 0) (w 2) (w 3)
    (ne 0 2 (by decide)) (ne 0 3 (by decide)) (ne 2 3 (by decide)) store scratch
  let framed:=Function.update (Function.update store (w 0) []) (w 2) (Encoding.frame (store (w 0)))
  have frameFinal : frameResult (extra+1) (w 0) (w 2) (w 3) store=framed := by
    funext r
    by_cases a : r=w 0
    · subst r;simp [framed,frameResult,w.injective.eq_iff]
    · by_cases b : r=w 2
      · subst r;simp [framed,frameResult,w.injective.eq_iff,buffer]
      · by_cases c : r=w 3
        · subst r;simp [framed,frameResult,w.injective.eq_iff,scratch]
        · simp [framed,frameResult,a,b,c]
  rw [frameFinal] at framing
  have reversing:=reverse_executes (extra+2) (w 2) (w 1) (ne 2 1 (by decide)) framed
  have sourceAt : framed (w 2)=Encoding.frame (store (w 0)) := by simp [framed]
  have outputAt : framed (w 1)=store (w 1) := by simp [framed,w.injective.eq_iff]
  rw [sourceAt,outputAt] at reversing
  have final : Function.update (Function.update framed (w 2) []) (w 1)
      ((Encoding.frame (store (w 0))).reverse++store (w 1))=
      Function.update (Function.update store (w 0) []) (w 1)
      ((Encoding.frame (store (w 0))).reverse++store (w 1)) := by
    funext r
    by_cases b : r=w 2
    · subst r;simp [w.injective.eq_iff,buffer]
    · simp [framed,Function.update_apply,b]
  rw [final] at reversing
  have combined:=framing.sequence reversing
  simpa only [emitBinary,Encoding.frame_length,
    show 5*(store (w 0)).length+4+1+(2*(2*(store (w 0)).length+1)+1)=9*(store (w 0)).length+8 by omega] using combined

abbrev BinaryPairEmitterWorkspace (extra : Nat) := Fin 5 ↪ Fin (extra+5)

def BinaryPairEmitterWorkspace.first (w : BinaryPairEmitterWorkspace extra) : BinaryEmitterWorkspace (extra+1) :=
  (⟨![0,2,3,4],by decide⟩ : Fin 4 ↪ Fin 5).trans w

def BinaryPairEmitterWorkspace.second (w : BinaryPairEmitterWorkspace extra) : BinaryEmitterWorkspace (extra+1) :=
  (⟨![1,2,3,4],by decide⟩ : Fin 4 ↪ Fin 5).trans w

def emitBinaryPair (extra : Nat) (w : BinaryPairEmitterWorkspace extra) : Routine (extra+3) :=
  sequence (emitBinary (extra+1) w.first) (emitBinary (extra+1) w.second)

theorem emitBinaryPair_executes (extra : Nat) (w : BinaryPairEmitterWorkspace extra)
    (store : Store (extra+3)) (buffer : store (w 3)=[]) (scratch : store (w 4)=[]) :
    Executes (emitBinaryPair extra w) store (9*((store (w 0)).length+(store (w 1)).length)+17)
      (Function.update (Function.update (Function.update store (w 0) []) (w 1) []) (w 2)
        ((Encoding.frame (store (w 0))++Encoding.frame (store (w 1))).reverse++store (w 2))) := by
  have first:=emitBinary_executes (extra+1) w.first store buffer scratch
  let middle:=Function.update (Function.update store (w 0) []) (w 2)
    ((Encoding.frame (store (w 0))).reverse++store (w 2))
  change Executes (emitBinary (extra+1) w.first) store (9*(store (w 0)).length+8) middle at first
  have second:=emitBinary_executes (extra+1) w.second middle
    (by simp [BinaryPairEmitterWorkspace.second,middle,w.injective.eq_iff,buffer])
    (by simp [BinaryPairEmitterWorkspace.second,middle,w.injective.eq_iff,scratch])
  have sourceAt : middle (w.second 0)=store (w 1) := by simp [BinaryPairEmitterWorkspace.second,middle,w.injective.eq_iff]
  rw [sourceAt] at second
  have final : Function.update (Function.update middle (w.second 0) []) (w.second 1)
      ((Encoding.frame (store (w 1))).reverse++middle (w.second 1))=
      Function.update (Function.update (Function.update store (w 0) []) (w 1) []) (w 2)
      ((Encoding.frame (store (w 0))++Encoding.frame (store (w 1))).reverse++store (w 2)) := by
    funext r
    by_cases a : r=w 2
    · subst r;simp [BinaryPairEmitterWorkspace.second,middle,List.reverse_append,List.append_assoc]
    · simp [BinaryPairEmitterWorkspace.second,middle,Function.update_apply,a]
  rw [final] at second
  simpa only [emitBinaryPair,show 9*(store (w 0)).length+8+1+(9*(store (w 1)).length+8)=
    9*((store (w 0)).length+(store (w 1)).length)+17 by omega] using first.sequence second

end Counting.StackMachine.Routine
