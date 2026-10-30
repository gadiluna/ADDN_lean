import Counting.X3CEncoding

namespace Counting.X3CEncoding

theorem tripleRaw_member_bound {q : Nat} (triple : Triple q) (element : Nat)
    (member : element ∈ tripleRaw triple) : element < 3*q := by
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact value.isLt

theorem triple_encoding_length {q : Nat} (triple : Triple q) :
    ((Encoding.list Encoding.natural).encode (tripleRaw triple)).length ≤ 6*(3*q).size+8 := by
  have bound := Encoding.natural_list_length_le (tripleRaw triple) (3*q)
    (fun element member => (tripleRaw_member_bound triple element member).le)
  rw [tripleRaw_length] at bound
  have threeBits : Nat.size 3 = 2 := by decide
  rw [threeBits] at bound
  omega

theorem triples_encoding_length {q : Nat} (triples : List (Triple q)) :
    ((Encoding.list (Encoding.list Encoding.natural)).encode (triples.map tripleRaw)).length ≤
      2*triples.length.size+1+triples.length*(6*(3*q).size+8) := by
  rw [Encoding.list_length, List.length_map]
  apply Nat.add_le_add_left
  induction triples with
  | nil => simp
  | cons head tail ih =>
    have bounded := triple_encoding_length head
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem encode_length_bound (input : Input) :
    (codec.encode input).length ≤
      3*input.1+2*(3*input.1).size+2*input.2.1.size+2+
        input.2.1*(6*(3*input.1).size+8) := by
  have triples := triples_encoding_length (inputTriples input)
  rw [inputTriples_length] at triples
  have table : ((Encoding.list Encoding.boolean).encode (List.replicate (3*input.1) true)).length =
      2*(3*input.1).size+1+3*input.1 := by
    rw [Encoding.list_length]
    simp [Encoding.boolean]
  change (rawCodec.encode (toRaw input)).length ≤ _
  change (((Encoding.list Encoding.boolean).encode (List.replicate (3*input.1) true)) ++
    ((Encoding.list (Encoding.list Encoding.natural)).encode ((inputTriples input).map tripleRaw))).length ≤ _
  rw [List.length_append, table]
  omega

/-- Output size alone is polynomial in the explicit finite parameters.
No running-time or machine simulation is asserted here. -/
theorem encode_length_polynomial (input : Input) :
    (codec.encode input).length ≤ 30*(input.1+input.2.1+1)^2 := by
  have bound := encode_length_bound input
  have universeSize : (3*input.1).size ≤ 3*input.1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have triplesSize : input.2.1.size ≤ input.2.1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have product := Nat.mul_le_mul_left input.2.1
    (show 6*(3*input.1).size+8 ≤ 18*input.1+8 by omega)
  nlinarith

end Counting.X3CEncoding
