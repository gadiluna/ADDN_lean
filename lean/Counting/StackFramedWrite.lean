import Counting.StackFramedList
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.FieldAccess
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Source, unary field index, raw replacement payload, and three empty
scratch registers. Source is replaced; index and replacement are consumed. -/
def writeRoles (w : Fin 6 ↪ Fin (extra+6)) : Fin 5 ↪ Fin (extra+6) where
  toFun i := w (![0,1,5,3,4] i)
  inj' := fun _ _ h => (by decide : Function.Injective (fun i : Fin 5 => (![0,1,5,3,4] i : Fin 6)))
    (w.injective h)

def writePayload (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4) :=
  sequence (frameRoutine (extra+3) (w 2) (w 5) (w 4))
    (sequence (replaceRoutine (extra+1) (writeRoles w)) (clear (w 5)))

def writePayloadResult (w : Fin 6 ↪ Fin (extra+6)) (store : Fin (extra+6) → List Bool) :
    Fin (extra+6) → List Bool :=
  Function.update (Function.update (Function.update store (w 1) []) (w 2) []) (w 0)
    (replaceFieldWord (store (w 0)) (store (w 1)).length (Encoding.frame (store (w 2))))

theorem writePayload_executes (extra : Nat) (w : Fin 6 ↪ Fin (extra+6))
    (store : Fin (extra+6) → List Bool)
    (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    ∃ time ≤ 5*(store (w 0)).length+3*(store (w 1)).length+17*(store (w 2)).length+21,
      Executes (writePayload extra w) store time (writePayloadResult w store) := by
  have distinct (i j : Fin 6) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  let framed := Function.update (Function.update store (w 2) []) (w 5) (Encoding.frame (store (w 2)))
  have framing : Executes (frameRoutine (extra+3) (w 2) (w 5) (w 4)) store
      (5*(store (w 2)).length+4) framed := by
    simpa only [e5,List.append_nil,framed] using frame_executes_updates (extra+3) (w 2) (w 5) (w 4)
      (distinct 2 5 (by decide)) (distinct 2 4 (by decide)) (distinct 5 4 (by decide)) store e4
  have atOther (i : Fin 6) (h2 : i≠2) (h5 : i≠5) : framed (w i)=store (w i) := by
    simp [framed,distinct i 2 h2,distinct i 5 h5]
  have atField : framed (writeRoles w 2)=Encoding.frame (store (w 2)) := by simp [writeRoles,framed]
  have atSource : framed (writeRoles w 0)=store (w 0) := atOther 0 (by decide) (by decide)
  have atIndex : framed (writeRoles w 1)=store (w 1) := atOther 1 (by decide) (by decide)
  let replaced := Function.update (Function.update framed (w 1) []) (w 0)
    (replaceFieldWord (store (w 0)) (store (w 1)).length (Encoding.frame (store (w 2))))
  have replacing : Executes (replaceRoutine (extra+1) (writeRoles w)) framed
      (replaceCost (store (w 0)) (store (w 1)) (Encoding.frame (store (w 2)))) replaced := by
    simpa only [atSource,atIndex,atField,atOther 0 (by decide) (by decide),atOther 1 (by decide) (by decide),show writeRoles w 0=w 0 from rfl,
      show writeRoles w 1=w 1 from rfl,replaced] using
      replace_executes (extra+1) (writeRoles w) framed
        (by change framed (w 3)=[]; rw [atOther 3 (by decide) (by decide),e3])
        (by change framed (w 4)=[]; rw [atOther 4 (by decide) (by decide),e4])
  have atFramed : replaced (w 5)=Encoding.frame (store (w 2)) := by
    simp [replaced,framed,w.injective.eq_iff]
  have cleaning := clear_executes (registers := extra+4) (w 5) replaced
  rw [atFramed] at cleaning
  have final : Function.update replaced (w 5) []=writePayloadResult w store := by
    funext r
    by_cases h0 : r=w 0
    · subst r; simp [replaced,writePayloadResult,w.injective.eq_iff]
    · by_cases h1 : r=w 1
      · subst r; simp [replaced,writePayloadResult,w.injective.eq_iff]
      · by_cases h2 : r=w 2
        · subst r; simp [replaced,framed,writePayloadResult,w.injective.eq_iff]
        · by_cases h5 : r=w 5
          · subst r; simp [writePayloadResult,w.injective.eq_iff,e5]
          · simp [replaced,framed,writePayloadResult,h0,h1,h2,h5]
  rw [final] at cleaning
  refine ⟨_,?_,framing.sequence (replacing.sequence cleaning)⟩
  have bounded := replaceCost_le (store (w 0)) (store (w 1)) (Encoding.frame (store (w 2)))
  rw [Encoding.frame_length] at bounded ⊢
  omega

theorem writePayload_framedList_executes {α : Type} (codec : Encoding.Codec α)
    (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) (store : Fin (extra+6) → List Bool)
    (values : List α) (index : Nat) (replacement : α) (valid : index<values.length)
    (source : store (w 0)=(Encoding.list (Encoding.framed codec)).encode values)
    (counter : store (w 1)=List.replicate (index+1) true)
    (payload : store (w 2)=codec.encode replacement)
    (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    ∃ time ≤ 5*((Encoding.list (Encoding.framed codec)).encode values).length+
        3*(index+1)+17*(codec.encode replacement).length+21,
      Executes (writePayload extra w) store time
        (Function.update (Function.update (Function.update store (w 1) []) (w 2) []) (w 0)
          ((Encoding.list (Encoding.framed codec)).encode (values.set index replacement))) := by
  simpa only [writePayloadResult,source,counter,payload,List.length_replicate,
    replaceFieldWord_framedList codec values index replacement valid] using
    writePayload_executes extra w store e3 e4 e5

end Counting.StackMachine.FieldAccess
