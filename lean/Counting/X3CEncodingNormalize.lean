import Counting.X3CEncodingDeduplicate

namespace Counting.X3CEncoding

def instanceRows {q m : Nat} (inst : X3C.Instance q m) : List (List Nat) :=
  List.ofFn (fun j => ((inst.triples j).sort (· ≤ ·)).map Fin.val)

def freshRow (q : Nat) : List Nat := [3*q,3*q+1,3*q+2]

theorem old_sorted_values {q : Nat} (elements : Finset (Fin (3*q))) :
    ((elements.image (X3C.oldElement q)).sort (· ≤ ·)).map Fin.val =
      (elements.sort (· ≤ ·)).map Fin.val := by
  have sorted := Finset.map_sort (X3C.oldElement q) elements (· ≤ ·) (· ≤ ·)
    (by intro a _ b _;rfl)
  rw [Finset.map_eq_image] at sorted
  rw [←sorted,List.map_map]
  rfl

theorem fresh_sorted_values (q : Nat) :
    ((X3C.freshTriple q).sort (· ≤ ·)).map Fin.val = freshRow q := by
  have sorted := Finset.map_sort (X3C.freshElement q) Finset.univ (· ≤ ·) (· ≤ ·)
    (by intro a _ b _;change a.val ≤ b.val ↔ 3*q+a.val ≤ 3*q+b.val;omega)
  rw [Finset.map_eq_image] at sorted
  rw [X3C.freshTriple,←sorted,List.map_map,Fin.sort_univ]
  simp [List.finRange,List.ofFn_succ,X3C.freshElement,freshRow]

theorem padded_instanceRows {q m : Nat} (inst : X3C.Instance q m) :
    instanceRows inst.pad = freshRow q :: instanceRows inst := by
  unfold instanceRows
  rw [List.ofFn_succ]
  apply congrArg₂ List.cons
  · exact fresh_sorted_values q
  · apply congrArg List.ofFn
    funext j
    exact old_sorted_values (inst.triples j)

theorem normalized_instanceRows {q m : Nat} (inst : X3C.RawInstance q m) :
    instanceRows inst.normalize = freshRow (q+1) :: freshRow q ::
      (firstIndices (rawRows inst)).map (rawRows inst) := by
  rw [X3C.RawInstance.normalize,padded_instanceRows,padded_instanceRows]
  congr 2
  exact deduplicate_rawRows inst

def normalizedInput (input : Input) : Input :=
  ⟨input.1+1+1,input.2.2.kept.card+1+1,
    ⟨input.2.2.normalize.triples,input.2.2.normalize.triple_card⟩⟩

/-- Both the explicit universe and every serialized row of normalization
are identified, including the order of the two forced fresh triples. -/
theorem normalizedInput_toRaw (input : Input) :
    toRaw (normalizedInput input) =
      (List.replicate (3*(input.1+1+1)) true,
        freshRow (input.1+1) :: freshRow input.1 ::
          (firstIndices (rawRows input.2.2)).map (rawRows input.2.2)) := by
  apply Prod.ext
  · rfl
  · change (List.ofFn (fun j => (⟨input.2.2.normalize.triples j,
      input.2.2.normalize.triple_card j⟩ : Triple (input.1+1+1)))).map tripleRaw = _
    rw [List.map_ofFn]
    exact normalized_instanceRows input.2.2

theorem normalizedInput_exactCover (input : Input) :
    (∃ chosen,(normalizedInput input).2.2.IsExactCover chosen) ↔
      ∃ chosen,input.2.2.IsExactCover chosen :=
  input.2.2.normalize_exactCover_iff

end Counting.X3CEncoding
