import Counting.PropagationEncodingBounds

namespace Counting.Executable

/-- Every finite schedule of level passes preserves the stored array size. -/
@[simp] theorem propagateLevels_size (vista : Vista) (weights : Array Nat) (levels : List Nat) :
    (levels.foldl (propagateLevel vista) weights).size=weights.size := by
  induction levels generalizing weights with
  | nil => rfl
  | cons level levels ih => simp only [List.foldl_cons,ih,propagateLevel_size]

/-- This bound covers prefixes of a descending schedule, as well as
arbitrary or repeated levels. No ordering assumption is needed. -/
theorem propagateLevels_value_bound (vista : Vista) (weights : Array Nat) (levels : List Nat) (M : Nat)
    (size : weights.size=vista.nodes.size) (bounded : ∀ i : Nat,weights[i]?.getD 0 ≤ M) (index : Nat) :
    (levels.foldl (propagateLevel vista) weights)[index]?.getD 0 ≤
      M*(vista.nodes.size+1)^levels.length := by
  induction levels generalizing weights M with
  | nil => simpa using bounded index
  | cons level levels ih =>
    rw [List.foldl_cons]
    have next:=ih (propagateLevel vista weights level) (M*(vista.nodes.size+1))
      ((propagateLevel_size vista level weights).trans size)
      (propagateLevel_value_bound vista weights level M size bounded)
    simpa only [List.length_cons,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using next

theorem propagateLevels_size_bound (vista : Vista) (weights : Array Nat) (levels : List Nat) (M : Nat)
    (size : weights.size=vista.nodes.size) (bounded : ∀ i : Nat,weights[i]?.getD 0 ≤ M) (index : Nat) :
    ((levels.foldl (propagateLevel vista) weights)[index]?.getD 0).size ≤
      M.size+levels.length*(vista.nodes.size+1).size := by
  have value:=propagateLevels_value_bound vista weights levels M size bounded index
  have positive : 0<(vista.nodes.size+1)^levels.length := pow_pos (by omega) _
  have power : (vista.nodes.size+1)^levels.length ≤
      (2^(vista.nodes.size+1).size)^levels.length :=
    Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self (vista.nodes.size+1))) _
  have high : M*(vista.nodes.size+1)^levels.length <
      2^(M.size+levels.length*(vista.nodes.size+1).size) := by
    calc
      _ < 2^M.size*(vista.nodes.size+1)^levels.length :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self M) positive
      _ ≤ 2^M.size*(2^(vista.nodes.size+1).size)^levels.length := Nat.mul_le_mul_left _ power
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring
  exact Nat.size_le.mpr (value.trans_lt high)

theorem propagateLevels_input_bit_bound (vista : Vista) (weights : Array Nat) (levels : List Nat)
    (size : weights.size=vista.nodes.size) (index : Nat) :
    ((levels.foldl (propagateLevel vista) weights)[index]?.getD 0).size ≤
      ((Encoding.array Encoding.natural).encode weights).length+1+
        levels.length*(vista.nodes.size+1).size := by
  let L:=((Encoding.array Encoding.natural).encode weights).length
  have bounded (i : Nat) : weights[i]?.getD 0 ≤ 2^L :=
    Nat.le_of_lt (Nat.size_le.mp (Encoding.naturalArray_entry_size_le weights i))
  have result:=propagateLevels_size_bound vista weights levels (2^L) size bounded index
  simpa only [Nat.size_pow,L] using result

/-- Complete framing is included, not only the binary payload. -/
theorem propagateLevels_encoded_length (vista : Vista) (weights : Array Nat) (levels : List Nat)
    (size : weights.size=vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (levels.foldl (propagateLevel vista) weights)).length ≤
      2*vista.nodes.size.size+1+vista.nodes.size*
        (2*(((Encoding.array Encoding.natural).encode weights).length+1+
          levels.length*(vista.nodes.size+1).size)+1) := by
  have result:=Encoding.naturalArray_length_le_bitWidth (levels.foldl (propagateLevel vista) weights)
    (((Encoding.array Encoding.natural).encode weights).length+1+
      levels.length*(vista.nodes.size+1).size) (by
      intro value member
      obtain ⟨index,inside,same⟩:=List.mem_iff_getElem.mp member
      have bound:=propagateLevels_input_bit_bound vista weights levels size index
      have inArray : index<(levels.foldl (propagateLevel vista) weights).size := by simpa using inside
      simpa [Array.getElem?_eq_getElem inArray,←same] using bound)
  simpa only [propagateLevels_size,size] using result

/-- Every prefix of a schedule with at most one pass per stored node has
polynomial encoded size, regardless of its level order or numeric labels. -/
theorem propagateLevels_encoded_polynomial (vista : Vista) (weights : Array Nat) (levels : List Nat)
    (size : weights.size=vista.nodes.size) (countLevels : levels.length ≤ vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (levels.foldl (propagateLevel vista) weights)).length ≤
      5*(((Encoding.array Encoding.natural).encode weights).length+1)^3 := by
  let L:=((Encoding.array Encoding.natural).encode weights).length
  have count:=Encoding.array_size_le_length Encoding.natural weights
    (by intro value _;rw [Encoding.natural_length];omega)
  change weights.size ≤ L at count
  rw [size] at count
  have sizeN : vista.nodes.size.size ≤ vista.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeNext : (vista.nodes.size+1).size ≤ vista.nodes.size+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have product:=Nat.mul_le_mul (countLevels.trans count)
    (show (vista.nodes.size+1).size ≤ L+1 by omega)
  have width : L+1+levels.length*(vista.nodes.size+1).size ≤ (L+1)^2 := by nlinarith only [product]
  have payload:=Nat.mul_le_mul count (Nat.add_le_add_right (Nat.mul_le_mul_left 2 width) 1)
  have result:=propagateLevels_encoded_length vista weights levels size
  change _ ≤ 2*vista.nodes.size.size+1+
    vista.nodes.size*(2*(L+1+levels.length*(vista.nodes.size+1).size)+1) at result
  change _ ≤ 5*(L+1)^3
  nlinarith only [result,payload,sizeN,count,Nat.zero_le L]

end Counting.Executable
