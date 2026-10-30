import Counting.ExternalCoefficientInputSemantics

namespace Counting.External.CoefficientMachine

theorem inputCoefficients_size (input : X3CEncoding.Input) :
    ∀ value∈inputCoefficients input,value.bits.length ≤ (3*input.1+1)*(X3C.base input.1).size := by
  intro value member
  simp only [inputCoefficients,coefficientValues,List.mem_cons,List.mem_map] at member
  rcases member with rfl|⟨row,inside,rfl⟩
  · rw [Encoding.bits_length]
    exact X3C.size_le_power_width _ _ _ (X3C.target_lt_base_power _)
  · exact input_rows_size_all input row inside

theorem natural_sequence_length_le (values : List Nat) (bound : Nat)
    (bounded : ∀ value∈values,value.bits.length ≤ bound) :
    (Encoding.sequence Encoding.natural values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil=>simp [Encoding.sequence]
  | cons head tail ih=>
    have first:=bounded head (by simp)
    have rest:=ih (fun value member=>bounded value (by simp [member]))
    simp only [Encoding.sequence,List.length_append,List.length_cons,Encoding.natural_length]
    rw [Encoding.bits_length] at first
    nlinarith only [first,rest]

theorem coefficient_width_bound (q L : Nat) (qBound : q ≤ L) :
    (3*q+1)*(X3C.base q).size ≤ 4*(L+4)^2 := by
  have baseBound : (X3C.base q).size ≤ q+3 := Nat.size_le.mpr Nat.lt_two_pow_self
  calc
    _ ≤ (3*(L+4)+1)*(L+4) := by apply Nat.mul_le_mul <;> omega
    _ ≤ _ := by nlinarith only [Nat.zero_le L]

theorem inputCoefficients_encoding_length (input : X3CEncoding.Input)
    (L : Nat) (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    ((Encoding.list Encoding.natural).encode (inputCoefficients input)).length ≤ 20*(L+4)^3 := by
  let width:=(3*input.1+1)*(X3C.base input.1).size
  have stream:=natural_sequence_length_le (inputCoefficients input) width (inputCoefficients_size input)
  have widthBound : width ≤ 4*(L+4)^2 := coefficient_width_bound _ _ qBound
  have count:=inputCoefficients_length input
  rw [count] at stream
  have header : (input.2.1+1).size ≤ input.2.1+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have streamLimit : (Encoding.sequence Encoding.natural (inputCoefficients input)).length ≤
      (L+4)*(8*(L+4)^2+1) := by
    apply stream.trans
    apply Nat.mul_le_mul <;> omega
  simp only [Encoding.list,List.length_append,Encoding.natural_length,count]
  nlinarith only [header,countBound,streamLimit,Nat.zero_le L]

end Counting.External.CoefficientMachine
