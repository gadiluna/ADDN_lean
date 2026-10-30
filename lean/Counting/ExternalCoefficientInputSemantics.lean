import Counting.ExternalCoefficientSemantics
import Counting.ExternalCoefficientStream

namespace Counting.External.CoefficientMachine

theorem powers_tripleRaw_le_ones {q : Nat} (triple : X3CEncoding.Triple q) :
    powers (X3C.base q) (X3CEncoding.tripleRaw triple) ≤ X3C.ones q := by
  rw [powers_tripleRaw]
  simp only [X3C.ones,X3C.digitValue,Nat.one_mul]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem triple_coefficient_size {q : Nat} (triple : X3CEncoding.Triple q) (positive : 1 ≤ q) :
    (X3C.high q+powers (X3C.base q) (X3CEncoding.tripleRaw triple)).bits.length ≤
      (3*q+1)*(X3C.base q).size := by
  have low:=powers_tripleRaw_le_ones triple
  have high : X3C.high q ≤ q*X3C.high q := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (X3C.high q) positive
  have target : X3C.high q+powers (X3C.base q) (X3CEncoding.tripleRaw triple) ≤ X3C.target q :=
    Nat.add_le_add high low
  rw [Encoding.bits_length]
  exact X3C.size_le_power_width _ _ _ (target.trans_lt (X3C.target_lt_base_power q))

theorem input_rows_three (input : X3CEncoding.Input) :
    ∀ row∈(X3CEncoding.toRaw input).2,row.length=3 := by
  intro row member
  obtain ⟨triple,_,rfl⟩:=List.mem_map.mp member
  exact X3CEncoding.tripleRaw_length triple

theorem input_rows_fit (input : X3CEncoding.Input) :
    ∀ row∈(X3CEncoding.toRaw input).2,∀ index∈row,index ≤ 3*input.1 := by
  intro row member index inside
  obtain ⟨triple,_,rfl⟩:=List.mem_map.mp member
  obtain ⟨element,_,rfl⟩:=List.mem_map.mp inside
  exact element.isLt.le

theorem input_rows_size (input : X3CEncoding.Input) (positive : 1 ≤ input.1) :
    ∀ row∈(X3CEncoding.toRaw input).2,
      (X3C.high input.1+powers (X3C.base input.1) row).bits.length ≤
        (3*input.1+1)*(X3C.base input.1).size := by
  intro row member
  obtain ⟨triple,_,rfl⟩:=List.mem_map.mp member
  exact triple_coefficient_size triple positive

theorem input_rows_size_all (input : X3CEncoding.Input) :
    ∀ row∈(X3CEncoding.toRaw input).2,
      (X3C.high input.1+powers (X3C.base input.1) row).bits.length ≤
        (3*input.1+1)*(X3C.base input.1).size := by
  by_cases positive : 1 ≤ input.1
  · exact input_rows_size input positive
  · intro row member
    obtain ⟨triple,_,rfl⟩:=List.mem_map.mp member
    have zero : input.1=0 := by omega
    have empty : triple.val=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e _
      have bound:=e.isLt
      omega
    have cardinality:=triple.property
    rw [empty,Finset.card_empty] at cardinality
    omega

def inputCoefficients (input : X3CEncoding.Input) : List Nat :=
  coefficientValues input.1 (X3CEncoding.toRaw input).2

theorem inputCoefficients_length (input : X3CEncoding.Input) :
    (inputCoefficients input).length=input.2.1+1 := by
  simp [inputCoefficients,coefficientValues,X3CEncoding.toRaw]

theorem inputCoefficients_instance {q m : Nat} (instanceData : X3C.Instance q m) :
    inputCoefficients ⟨q,m,⟨instanceData.triples,instanceData.triple_card⟩⟩=
      instanceData.coefficient none::List.ofFn (fun j=>instanceData.coefficient (some j)) := by
  simp only [inputCoefficients,coefficientValues,X3CEncoding.toRaw,X3CEncoding.inputTriples,
    List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_def]
  rw [powers_instance_triple]
  rfl

end Counting.External.CoefficientMachine
