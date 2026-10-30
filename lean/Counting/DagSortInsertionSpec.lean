import Counting.StackDagSortRecord
import Counting.DagCanonicalSortSpec

namespace Counting.StackMachine.DagUpdate.Sort

def recordLE (query current : Record) : Bool := Executable.lexLE query.2.key current.2.key

def scanRecords (query : Record) (inserted : Bool) : List Record → List Record×Bool
  | [] => ([],inserted)
  | current::rest =>
    let before := recordLE query current
    let next := scanRecords query (inserted || before) rest
    ((if !inserted && before then [query,current] else [current])++next.1,next.2)

def completedRecords (query : Record) (inserted : Bool) (records : List Record) : List Record :=
  (scanRecords query inserted records).1++
    (if (scanRecords query inserted records).2 then [] else [query])

theorem scanRecords_inserted (query : Record) (records : List Record) :
    scanRecords query true records=(records,true) := by
  induction records with
  | nil => rfl
  | cons current rest ih => simp [scanRecords,ih]

theorem completedRecords_inserted (query : Record) (records : List Record) :
    completedRecords query true records=records := by
  simp [completedRecords,scanRecords_inserted]

/-- The complete physical scan and its final pending emission are exactly
stable ordered insertion, including equal keys. Original indices are retained. -/
theorem completedRecords_orderedInsert (query : Record) (records : List Record) :
    completedRecords query false records=List.orderedInsert (fun a b=>recordLE a b=true) query records := by
  induction records with
  | nil => rfl
  | cons current rest ih =>
    cases before : recordLE query current with
    | false =>
      simpa [completedRecords,scanRecords,before,List.orderedInsert_cons] using congrArg (List.cons current) ih
    | true => simp [completedRecords,scanRecords,before,scanRecords_inserted,List.orderedInsert_cons]

theorem scanRecords_length_le (query : Record) (inserted : Bool) (records : List Record) :
    (scanRecords query inserted records).1.length≤records.length+1 := by
  cases inserted with
  | true => simp [scanRecords_inserted]
  | false =>
    have finished := List.orderedInsert_length (fun a b=>recordLE a b=true) records query
    rw [←completedRecords_orderedInsert,completedRecords,List.length_append] at finished
    omega

end Counting.StackMachine.DagUpdate.Sort
