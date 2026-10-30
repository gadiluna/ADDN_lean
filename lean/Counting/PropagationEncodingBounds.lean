import Counting.PropagationValueBounds

namespace Counting.Encoding

theorem naturalArray_entry_size_le (values : Array Nat) (index : Nat) :
    (values[index]?.getD 0).size ≤ ((array natural).encode values).length := by
  by_cases inside : index<values.size
  · have member : values[index]∈values.toList := Array.mem_toList_iff.mpr (Array.getElem_mem inside)
    have bound:=array_member_length_le natural values values[index] member
    simp only [natural_length] at bound
    simp only [Array.getElem?_eq_getElem inside,Option.getD_some]
    omega
  · simp [Array.getElem?_eq_none (Nat.le_of_not_lt inside)]

theorem naturalArray_length_le_bitWidth (values : Array Nat) (bitWidth : Nat)
    (bounded : ∀ value∈values.toList,value.size ≤ bitWidth) :
    ((array natural).encode values).length ≤
      2*values.size.size+1+values.size*(2*bitWidth+1) := by
  have sumBound:=List.sum_le_sum (l:=values.toList) (f:=fun value=>(natural.encode value).length)
    (g:=fun _=>2*bitWidth+1) (by intro value member;rw [natural_length];have := bounded value member;omega)
  simp only [List.map_const',List.sum_replicate,Array.length_toList,smul_eq_mul] at sumBound
  rw [array_length]
  omega

end Counting.Encoding

namespace Counting.Executable

theorem propagateDown_input_bit_bound (vista : Vista) (weights : Array Nat) (rounds : Nat)
    (size : weights.size=vista.nodes.size) (index : Nat) :
    ((propagateDown vista rounds weights)[index]?.getD 0).size ≤
      ((Encoding.array Encoding.natural).encode weights).length+1+rounds*(vista.nodes.size+1).size := by
  let L:=((Encoding.array Encoding.natural).encode weights).length
  have bounded (i : Nat) : weights[i]?.getD 0 ≤ 2^L :=
    Nat.le_of_lt (Nat.size_le.mp (Encoding.naturalArray_entry_size_le weights i))
  have result:=propagateDown_size_bound vista weights rounds (2^L) size bounded index
  simpa only [Nat.size_pow,L] using result

/-- A bound for the entire framed array after any number of backward levels. -/
theorem propagateDown_encoded_length (vista : Vista) (weights : Array Nat) (rounds : Nat)
    (size : weights.size=vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (propagateDown vista rounds weights)).length ≤
      2*vista.nodes.size.size+1+vista.nodes.size*
        (2*(((Encoding.array Encoding.natural).encode weights).length+1+
          rounds*(vista.nodes.size+1).size)+1) := by
  have result:=Encoding.naturalArray_length_le_bitWidth (propagateDown vista rounds weights)
    (((Encoding.array Encoding.natural).encode weights).length+1+rounds*(vista.nodes.size+1).size) (by
      intro value member
      obtain ⟨index,inside,same⟩:=List.mem_iff_getElem.mp member
      have bound:=propagateDown_input_bit_bound vista weights rounds size index
      have inArray : index<(propagateDown vista rounds weights).size := by simpa using inside
      simpa [Array.getElem?_eq_getElem inArray,←same] using bound)
  simpa only [propagateDown_size,size] using result

/-- A bounded descending pass keeps the complete binary array polynomial
in its original encoding length. No assumption on the values' magnitude
or positivity, or on graph validity, is needed. -/
theorem propagateDown_encoded_polynomial (vista : Vista) (weights : Array Nat) (rounds : Nat)
    (size : weights.size=vista.nodes.size) (depth : rounds ≤ vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (propagateDown vista rounds weights)).length ≤
      5*(((Encoding.array Encoding.natural).encode weights).length+1)^3 := by
  let L:=((Encoding.array Encoding.natural).encode weights).length
  have count:=Encoding.array_size_le_length Encoding.natural weights
    (by intro value _;rw [Encoding.natural_length];omega)
  change weights.size ≤ L at count
  rw [size] at count
  have sizeN : vista.nodes.size.size ≤ vista.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeNext : (vista.nodes.size+1).size ≤ vista.nodes.size+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have product:=Nat.mul_le_mul (depth.trans count) (show (vista.nodes.size+1).size ≤ L+1 by omega)
  have width : L+1+rounds*(vista.nodes.size+1).size ≤ (L+1)^2 := by nlinarith only [product]
  have payload:=Nat.mul_le_mul count (Nat.add_le_add_right (Nat.mul_le_mul_left 2 width) 1)
  have result:=propagateDown_encoded_length vista weights rounds size
  change _ ≤ 2*vista.nodes.size.size+1+vista.nodes.size*(2*(L+1+rounds*(vista.nodes.size+1).size)+1) at result
  change _ ≤ 5*(L+1)^3
  nlinarith only [result,payload,sizeN,count,Nat.zero_le L]

end Counting.Executable
