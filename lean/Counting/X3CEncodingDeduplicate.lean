import Counting.X3CEncoding

/-! Exact first-occurrence order for the serialized X3C normalization.
The prefix-membership test below is the specification of the concrete
binary-row scanner, not a machine-time claim. -/
namespace Counting.X3CEncoding

def firstIndices {α : Type} [DecidableEq α] {m : Nat} (rows : Fin m → α) : List (Fin m) :=
  (List.finRange m).filter (fun j => decide (rows j ∉ (List.ofFn rows).take j.val))

theorem no_previous_iff {α : Type} [DecidableEq α] {m : Nat}
    (rows : Fin m → α) (j : Fin m) :
    rows j ∉ (List.ofFn rows).take j.val ↔ ∀ i, rows i = rows j → j ≤ i := by
  constructor
  · intro absent i equal
    by_contra below
    have before : i.val < j.val := by omega
    apply absent
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.val, by simp only [List.length_ofFn]; omega, ?_⟩
    simpa only [List.getElem_ofFn] using equal
  · intro minimal member
    obtain ⟨i, inside, equal⟩ := List.mem_take_iff_getElem.mp member
    have bound : i < m := by simpa only [List.length_ofFn] using (lt_of_lt_of_le inside (min_le_right _ _))
    have chosen := minimal ⟨i,bound⟩ (by simpa only [List.getElem_ofFn] using equal)
    change j.val ≤ i at chosen
    have before : i < j.val := lt_of_lt_of_le inside (min_le_left _ _)
    omega

theorem mem_firstIndices {α : Type} [DecidableEq α] {m : Nat}
    (rows : Fin m → α) (j : Fin m) :
    j ∈ firstIndices rows ↔ ∀ i, rows i = rows j → j ≤ i := by
  simp only [firstIndices,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  exact no_previous_iff rows j

theorem firstIndices_sorted {α : Type} [DecidableEq α] {m : Nat} (rows : Fin m → α) :
    (firstIndices rows).SortedLT :=
  ((List.sortedLT_finRange m).pairwise.filter _).sortedLT

theorem tripleRaw_injective {q : Nat} : Function.Injective (@tripleRaw q) := by
  intro first second equal
  have same := congrArg (tripleFromRaw q) equal
  exact Option.some.inj (by simpa only [tripleFromRaw_tripleRaw] using same)

def rawRows {q m : Nat} (inst : X3C.RawInstance q m) : Fin m → List Nat :=
  fun j => tripleRaw ⟨inst.triples j,inst.triple_card j⟩

theorem rawRows_eq_iff {q m : Nat} (inst : X3C.RawInstance q m) (i j : Fin m) :
    rawRows inst i = rawRows inst j ↔ inst.triples i = inst.triples j := by
  constructor
  · intro equal
    exact congrArg Subtype.val (tripleRaw_injective equal)
  · intro equal
    apply congrArg tripleRaw
    exact Subtype.ext equal

theorem firstIndices_kept {q m : Nat} (inst : X3C.RawInstance q m) :
    firstIndices (rawRows inst) = inst.kept.sort (· ≤ ·) := by
  apply (firstIndices_sorted _).eq_of_mem_iff inst.kept.sortedLT_sort
  intro j
  simp only [mem_firstIndices,Finset.mem_sort,X3C.RawInstance.kept,
    Finset.mem_filter,Finset.mem_univ,true_and,rawRows_eq_iff]

/-- The exact serialized row order is first-occurrence order, matching the
finite-set order embedding used in the original normalization. -/
theorem deduplicate_rawRows {q m : Nat} (inst : X3C.RawInstance q m) :
    List.ofFn (rawRows (⟨inst.deduplicate.triples,inst.deduplicate.triple_card⟩ :
      X3C.RawInstance q inst.kept.card)) =
      (firstIndices (rawRows inst)).map (rawRows inst) := by
  rw [firstIndices_kept,←Finset.listMap_orderEmbOfFin_finRange inst.kept rfl,
    List.map_map,List.ofFn_eq_map]
  rfl

end Counting.X3CEncoding
