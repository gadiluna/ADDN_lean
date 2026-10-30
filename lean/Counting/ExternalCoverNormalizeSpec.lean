import Counting.X3CEncodingDeduplicate
import Counting.ExternalMatchingParser

namespace Counting.External.CoverNormalization
set_option backward.isDefEq.respectTransparency false

def freshRows {α : Type} [DecidableEq α] (before : List α) : List α → List α
  | [] => []
  | row::rest => if row∈before then freshRows (before++[row]) rest
      else row::freshRows (before++[row]) rest

theorem freshRows_length {α : Type} [DecidableEq α] (before rows : List α) :
    (freshRows before rows).length ≤ rows.length := by
  induction rows generalizing before with
  | nil => simp [freshRows]
  | cons row rest ih =>
    have tail := ih (before++[row])
    simp only [freshRows,List.length_cons]
    split
    · omega
    · simp only [List.length_cons];omega

theorem freshRows_sequence_length (before rows : List MatchingVerification.RawClause) :
    (Encoding.sequence MatchingVerification.clauseCodec (freshRows before rows)).length ≤
      (Encoding.sequence MatchingVerification.clauseCodec rows).length := by
  induction rows generalizing before with
  | nil => simp [freshRows]
  | cons row rest ih =>
    have tail := ih (before++[row])
    simp only [freshRows]
    split <;> simp only [Encoding.sequence,List.length_append] <;> omega

theorem freshRows_ofFn {α : Type} [DecidableEq α] (m : Nat) (rows : Fin m → α)
    (before : List α) :
    freshRows before (List.ofFn rows)=
      ((List.finRange m).filter (fun j => decide (rows j ∉ before++(List.ofFn rows).take j.val))).map rows := by
  induction m generalizing before with
  | zero => simp [freshRows]
  | succ m ih =>
    rw [List.ofFn_succ]
    simp only [freshRows]
    rw [ih (fun j => rows j.succ) (before++[rows 0])]
    simp only [List.finRange_succ,List.filter_cons,List.filter_map,
      Fin.val_zero,List.take_zero,List.append_nil]
    simp only [List.append_assoc,List.singleton_append]
    by_cases present : rows 0∈before
    · simp [present,Function.comp_def]
    · simp [present,Function.comp_def]

theorem freshRows_firstIndices {α : Type} [DecidableEq α] {m : Nat} (rows : Fin m → α) :
    freshRows [] (List.ofFn rows)=(X3CEncoding.firstIndices rows).map rows := by
  simpa only [X3CEncoding.firstIndices,List.nil_append] using freshRows_ofFn m rows []

theorem freshRows_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α→β) (injective : Function.Injective f) (before rows : List α) :
    (freshRows before rows).map f=freshRows (before.map f) (rows.map f) := by
  induction rows generalizing before with
  | nil=>rfl
  | cons row rest ih=>
    have member : f row∈before.map f ↔ row∈before := by
      simp only [List.mem_map,injective.eq_iff,exists_eq_right]
    simp only [List.map_cons,freshRows,member]
    split <;> simp only [List.map_cons,ih,List.map_append,List.map_nil]

end Counting.External.CoverNormalization
