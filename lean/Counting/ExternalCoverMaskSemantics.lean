import Counting.ExternalCoverWitness
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Counting.External.CoverVerification
open scoped BigOperators

/-- Number of selected rows containing the queried universe element. -/
def hits : List (List Nat) → List Bool → Nat → Nat
  | [],_,_ => 0
  | _,[],_ => 0
  | row::rows,bit::bits,element => (if bit && row.contains element then 1 else 0)+hits rows bits element

theorem hits_ofFn {m : Nat} (rows : Fin m → List Nat) (mask : Fin m → Bool) (element : Nat) :
    hits (List.ofFn rows) (List.ofFn mask) element=∑ j,if mask j && (rows j).contains element then 1 else 0 := by
  induction m with
  | zero => simp [hits]
  | succ m ih =>
    rw [List.ofFn_succ,List.ofFn_succ,hits,Fin.sum_univ_succ]
    rw [ih]

@[simp] theorem triple_contains {q : Nat} (triple : X3CEncoding.Triple q) (element : Fin (3*q)) :
    (X3CEncoding.tripleRaw triple).contains element.val=decide (element∈triple.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [X3CEncoding.tripleRaw,List.contains_eq_mem,List.mem_map,
    Finset.mem_sort,decide_eq_true_eq]
  constructor
  · rintro ⟨a,member,equal⟩
    have same : a=element := Fin.ext equal
    simpa only [same] using member
  · intro member
    exact ⟨element,member,rfl⟩

theorem mask_ofFn {m : Nat} (mask : List Bool) (sized : mask.length=m) :
    List.ofFn (fun j : Fin m=>mask[j.val]?.getD false)=mask := by
  apply List.ext_getElem?
  intro j
  by_cases inside : j<m
  · have bounded : j<mask.length := by omega
    simp only [List.getElem?_ofFn,dif_pos inside,List.getElem?_eq_getElem bounded,Option.getD_some]
  · have outside : mask.length≤j := by omega
    simp only [List.getElem?_ofFn,dif_neg inside,List.getElem?_eq_none outside]

theorem hits_typed (input : X3CEncoding.Input) (mask : List Bool) (sized : mask.length=input.2.1)
    (element : Fin (3*input.1)) :
    hits (X3CEncoding.toRaw input).2 mask element.val=
      ((ThreeDMEncoding.selected input.2.1 mask).filter (fun j=>element∈input.2.2.triples j)).card := by
  let rows := fun j : Fin input.2.1=>X3CEncoding.tripleRaw ⟨input.2.2.triples j,input.2.2.triple_card j⟩
  have rowsEq : (X3CEncoding.toRaw input).2=List.ofFn rows := by
    simp only [X3CEncoding.toRaw,X3CEncoding.inputTriples,List.map_ofFn,rows,Function.comp_def]
  rw [rowsEq]
  conv_lhs => rw [←mask_ofFn mask sized,hits_ofFn]
  simp only [rows,triple_contains,Bool.and_eq_true,decide_eq_true_eq]
  rw [ThreeDMEncoding.selected,Finset.filter_filter,Finset.card_filter]

/-- The row-loop condition is exactly the mathematical certificate on
canonical inputs, including an empty universe. -/
theorem checkMask_hits (input : X3CEncoding.Input) (mask : List Bool) (sized : mask.length=input.2.1) :
    checkMask input mask=true ↔ ∀ element : Fin (3*input.1),hits (X3CEncoding.toRaw input).2 mask element.val=1 := by
  simp only [checkMask_iff,sized,true_and,X3C.RawInstance.IsExactCover]
  simp only [hits_typed input mask sized]

end Counting.External.CoverVerification
