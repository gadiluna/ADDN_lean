import Counting.ExternalThreeDMEncoding
import Counting.X3CEncoding

namespace Counting.External.ThreeDMEncoding

def coverInput (input : Input) : X3CEncoding.Input := ⟨input.1,input.2.1,input.2.2.toX3C⟩

theorem coverInput_yes_iff (input : Input) :
    (∃ chosen,(coverInput input).2.2.IsExactCover chosen) ↔ input.2.2.Yes := input.2.2.toX3C_yes_iff

@[simp] theorem element_value {q : Nat} (part : Fin 3) (value : Fin q) :
    (ThreeDM.element part value).val=part.val*q+value.val := by
  simp [ThreeDM.element,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

theorem triple_sorted {q m : Nat} (inst : ThreeDM q m) (j : Fin m) :
    (inst.toX3C.triples j).sort (·≤·)=[ThreeDM.element 0 (inst.edge j 0),ThreeDM.element 1 (inst.edge j 1),ThreeDM.element 2 (inst.edge j 2)] := by
  have sorted : ([ThreeDM.element 0 (inst.edge j 0),ThreeDM.element 1 (inst.edge j 1),ThreeDM.element 2 (inst.edge j 2)] : List (Fin (3*q))).SortedLT := by
    apply List.Pairwise.sortedLT
    have a := (inst.edge j 0).isLt
    have b := (inst.edge j 1).isLt
    have c := (inst.edge j 2).isLt
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
    · intro value member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      all_goals
        rw [Fin.lt_def,element_value,element_value]
        norm_num
        omega
    · intro value member
      have same : value=ThreeDM.element 2 (inst.edge j 2) := by simpa only [List.mem_singleton] using member
      subst value
      rw [Fin.lt_def,element_value,element_value]
      norm_num
      omega
    · intro value member
      simp at member
  apply (Finset.sortedLT_sort _).eq_of_mem_iff sorted
  intro value
  simp only [Finset.mem_sort,List.mem_cons,List.not_mem_nil,or_false,ThreeDM.toX3C,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨part,equal⟩
    fin_cases part <;> simp_all
  · rintro (equal|equal|equal)
    · exact ⟨0,equal.symm⟩
    · exact ⟨1,equal.symm⟩
    · exact ⟨2,equal.symm⟩

theorem cover_tripleRaw {q m : Nat} (inst : ThreeDM q m) (j : Fin m) :
    X3CEncoding.tripleRaw ⟨inst.toX3C.triples j,inst.toX3C.triple_card j⟩=
      [(inst.edge j 0).val,q+(inst.edge j 1).val,2*q+(inst.edge j 2).val] := by
  rw [X3CEncoding.tripleRaw,triple_sorted]
  simp [element_value]

def coverRows (q : Nat) (triples : List (Triple q)) : List (List Nat) :=
  triples.map (fun triple=>[(triple 0).val,q+(triple 1).val,2*q+(triple 2).val])

theorem coverInput_toRaw (input : Input) :
    X3CEncoding.toRaw (coverInput input)=(List.replicate (3*input.1) true,coverRows input.1 (inputTriples input)) := by
  apply Prod.ext
  · rfl
  · change (List.ofFn (fun j=>⟨input.2.2.toX3C.triples j,input.2.2.toX3C.triple_card j⟩)).map X3CEncoding.tripleRaw=_
    simp only [List.map_ofFn,Function.comp_def,cover_tripleRaw,coverRows,inputTriples]

theorem coverRows_length {q : Nat} (triples : List (Triple q)) : (coverRows q triples).length=triples.length := by simp [coverRows]

end Counting.External.ThreeDMEncoding
