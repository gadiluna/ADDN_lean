import Counting.StackFrameReadPreserving
import Counting.StackFrameReplace
import Counting.EncodingRationalRows

namespace Counting.StackMachine.FieldAccess

theorem skipMany_framed {α : Type} (codec : Encoding.Codec α)
    (count : Nat) (values : List α) :
    skipMany count (Encoding.sequence (Encoding.framed codec) values)=
      Encoding.sequence (Encoding.framed codec) (values.drop count) := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values with
      | nil => simp [Encoding.sequence]
      | cons value values =>
          simp only [skipMany,Encoding.sequence,Encoding.framed,skipRest_frame,List.drop_succ_cons]
          exact ih values

theorem selectPayload_framed {α : Type} (codec : Encoding.Codec α)
    (values : List α) (index : Nat) :
    selectPayload (Encoding.sequence (Encoding.framed codec) values) index=
      (values[index]?).map codec.encode := by
  rw [selectPayload,skipMany_framed,←List.head?_drop]
  cases values.drop index with
  | nil => rfl
  | cons value values => simp [Encoding.sequence,Encoding.framed,Encoding.unframe_frame]

/-- The list header occupies field zero; the payload of field index+1 is the
unchanged canonical encoding of the indexed value. -/
theorem selectPayload_framedList {α : Type} (codec : Encoding.Codec α)
    (values : List α) (index : Nat) :
    selectPayload ((Encoding.list (Encoding.framed codec)).encode values) (index+1)=
      (values[index]?).map codec.encode := by
  change (Encoding.unframe (skipMany index (skipRest
    (Encoding.frame values.length.bits++Encoding.sequence (Encoding.framed codec) values)))).map (·.1)=_
  rw [skipRest_frame]
  exact selectPayload_framed codec values index

theorem replaceFieldWord_framed {α : Type} (codec : Encoding.Codec α)
    (values : List α) (index : Nat) (replacement : α) (valid : index<values.length) :
    replaceFieldWord (Encoding.sequence (Encoding.framed codec) values) index
      (Encoding.frame (codec.encode replacement))=
      Encoding.sequence (Encoding.framed codec) (values.set index replacement) := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => simp at valid
      | cons value values =>
          simp [replaceFieldWord,frontMany,skipMany,Encoding.sequence,Encoding.framed,skipRest_frame]
  | succ index ih =>
      cases values with
      | nil => simp at valid
      | cons value values =>
          have inside : index<values.length := by simpa using valid
          have tail := ih values inside
          simp only [replaceFieldWord,frontMany,skipMany,Encoding.sequence,Encoding.framed,
            frameFront_frame,skipRest_frame,List.set_cons_succ,List.append_assoc] at tail ⊢
          rw [tail]

theorem replaceFieldWord_framedList {α : Type} (codec : Encoding.Codec α)
    (values : List α) (index : Nat) (replacement : α) (valid : index<values.length) :
    replaceFieldWord ((Encoding.list (Encoding.framed codec)).encode values) (index+1)
      (Encoding.frame (codec.encode replacement))=
      (Encoding.list (Encoding.framed codec)).encode (values.set index replacement) := by
  change frontMany (index+1) (Encoding.frame values.length.bits++Encoding.sequence (Encoding.framed codec) values)++
    Encoding.frame (codec.encode replacement)++skipRest (skipMany (index+1)
      (Encoding.frame values.length.bits++Encoding.sequence (Encoding.framed codec) values))=_
  rw [frontMany,frameFront_frame,skipRest_frame,skipMany,skipRest_frame]
  simp only [List.append_assoc]
  have replaced := replaceFieldWord_framed codec values index replacement valid
  simp only [replaceFieldWord,List.append_assoc] at replaced
  rw [replaced]
  simp only [Encoding.list,List.length_set,Encoding.natural]

/-- A machine read through the canonical container, preserving the original
container, unary index, external registers and output tails. -/
theorem preservingRead_framedList_executes {α : Type} (codec : Encoding.Codec α)
    (extra : Nat) (w : Fin 8 ↪ Fin (extra+8)) (store : Fin (extra+8) → List Bool)
    (values : List α) (index : Nat)
    (source : store (w 0)=(Encoding.list (Encoding.framed codec)).encode values)
    (counter : store (w 1)=List.replicate (index+1) true)
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) :
    ∃ time ≤ 10*((Encoding.list (Encoding.framed codec)).encode values).length+8*(index+1)+14,
      Routine.Executes (preservingRead extra w) store time
        (Function.update (Function.update store (w 2)
          (((values[index]?).map codec.encode).getD []++store (w 2)))
          (w 3) ((values[index]?).isSome::store (w 3))) := by
  simpa only [source,counter,List.length_replicate,selectPayload_framedList,Option.isSome_map] using
    preservingRead_executes extra w store e4 e5 e6 e7

/-- Actual replacement through the canonical container. The supplied field
already includes its outer frame, exactly as consumed by replaceRoutine. -/
theorem replace_framedList_executes {α : Type} (codec : Encoding.Codec α)
    (extra : Nat) (w : Fin 5 ↪ Fin (extra+5)) (store : Fin (extra+5) → List Bool)
    (values : List α) (index : Nat) (replacement : α) (valid : index<values.length)
    (source : store (w 0)=(Encoding.list (Encoding.framed codec)).encode values)
    (counter : store (w 1)=List.replicate (index+1) true)
    (field : store (w 2)=Encoding.frame (codec.encode replacement))
    (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) :
    ∃ time ≤ 5*((Encoding.list (Encoding.framed codec)).encode values).length+
        3*(index+1)+5*(Encoding.frame (codec.encode replacement)).length+8,
      Routine.Executes (replaceRoutine extra w) store time
        (Function.update (Function.update store (w 1) []) (w 0)
          ((Encoding.list (Encoding.framed codec)).encode (values.set index replacement))) := by
  refine ⟨replaceCost ((Encoding.list (Encoding.framed codec)).encode values)
    (List.replicate (index+1) true) (Encoding.frame (codec.encode replacement)),?_,?_⟩
  · simpa only [source,counter,field,List.length_replicate] using
      replaceCost_le (store (w 0)) (store (w 1)) (store (w 2))
  · simpa only [source,counter,field,List.length_replicate,
      replaceFieldWord_framedList codec values index replacement valid] using
      replace_executes extra w store e3 e4

end Counting.StackMachine.FieldAccess
