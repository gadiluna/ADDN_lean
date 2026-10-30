import Counting.DagSortInsertionSpec

namespace Counting.StackMachine.DagUpdate.Sort

theorem sequence_append {α : Type} (codec : Encoding.Codec α) (first second : List α) :
    Encoding.sequence codec (first++second)=Encoding.sequence codec first++Encoding.sequence codec second := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp [Encoding.sequence,ih,List.append_assoc]

theorem orderedInsert_encoded_length (query : Record) (records : List Record) :
    (Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records)).length=
      (recordCodec.encode query).length+(Encoding.sequence recordCodec records).length := by
  induction records with
  | nil => simp [List.orderedInsert,Encoding.sequence]
  | cons head tail ih =>
    rw [List.orderedInsert_cons]
    split_ifs with h
    · simp [Encoding.sequence]
    · simp only [Encoding.sequence,List.length_append,ih]
      omega

theorem scanRecords_encoded_length_le (query : Record) (inserted : Bool) (records : List Record) :
    (Encoding.sequence recordCodec (scanRecords query inserted records).1).length≤
      (recordCodec.encode query).length+(Encoding.sequence recordCodec records).length := by
  cases inserted with
  | true => simp [scanRecords_inserted]
  | false =>
    have full := orderedInsert_encoded_length query records
    rw [←completedRecords_orderedInsert,completedRecords,sequence_append,List.length_append] at full
    omega

end Counting.StackMachine.DagUpdate.Sort
