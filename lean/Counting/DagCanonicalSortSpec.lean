import Counting.DagKeySort

namespace Counting.Executable

private theorem orderedInsert_skip {α : Type*} (rel : α→α→Prop) [DecidableRel rel]
    (value : α) (before after : List α) (skipped : ∀ item∈before,¬rel value item) :
    List.orderedInsert rel value (before++after)=before++List.orderedInsert rel value after := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
    have no := skipped head (by simp)
    simp only [List.cons_append,List.orderedInsert_cons,if_neg no]
    rw [ih (fun item member=>skipped item (by simp [member]))]

/-- Stable merge sort and insertion sort agree for a total preorder.
Antisymmetry is unnecessary: the proof uses the actual stable split around
the inserted element, so records with equal keys retain their input order. -/
theorem mergeSort_eq_stableInsertion {α : Type*} (compare : α→α→Bool)
    (trans : ∀ a b c,compare a b=true → compare b c=true → compare a c=true)
    (total : ∀ a b,compare a b=true ∨ compare b a=true) (values : List α) :
    values.mergeSort compare=values.insertionSort (fun a b=>compare a b=true) := by
  have totalBool : ∀ a b,compare a b || compare b a := by
    intro a b
    simpa only [Bool.or_eq_true] using total a b
  induction values with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨before,after,whole,rest,skipped⟩ := List.mergeSort_cons trans totalBool head tail
    have sorted := List.pairwise_mergeSort trans totalBool (head::tail)
    rw [whole,List.pairwise_append] at sorted
    have follows := (List.pairwise_cons.mp sorted.2.1).1
    rw [whole,List.insertionSort_cons,←ih,rest,orderedInsert_skip]
    · congr 1
      cases after with
      | nil => rfl
      | cons first remaining =>
        exact (List.orderedInsert_cons_of_le (fun a b=>compare a b=true) remaining (follows first (by simp))).symm
    · intro item member equal
      have no := skipped item member
      simp [equal] at no

/-- The executable's local index list has an exact stable insertion-sort
implementation even when several indices denote identical signatures. -/
theorem canonical_ordered_indices (vista : Vista) (mapping : Array Nat) (indices : List Nat) :
    indices.mergeSort (fun i j=>lexLE (referenceMap mapping (vista.node i)).key
      (referenceMap mapping (vista.node j)).key)=
    indices.insertionSort (fun i j=>lexLE (referenceMap mapping (vista.node i)).key
      (referenceMap mapping (vista.node j)).key=true) := by
  apply mergeSort_eq_stableInsertion
  · intro a b c first second
    exact lexLE_trans first second
  · intro a b
    exact lexLE_total _ _

/-- A physical loop may scan a reversed input stream and insert each
record at the first greater-or-equal key. This is the same stable order,
including repeated signatures and arbitrary original index lists. -/
theorem canonical_ordered_indices_fold (vista : Vista) (mapping : Array Nat) (indices : List Nat) :
    indices.mergeSort (fun i j=>lexLE (referenceMap mapping (vista.node i)).key
      (referenceMap mapping (vista.node j)).key)=
    indices.reverse.foldl (fun sorted index=>List.orderedInsert
      (fun i j=>lexLE (referenceMap mapping (vista.node i)).key
        (referenceMap mapping (vista.node j)).key=true) index sorted) [] := by
  rw [canonical_ordered_indices,List.insertionSort,List.foldr_eq_foldl_reverse]

end Counting.Executable
