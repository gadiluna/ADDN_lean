import Counting.DagReferenceEncodingBounds

namespace Counting.Executable

private theorem prefix_sequence_length {α : Type} (codec : Encoding.Codec α) (visited source : List α)
    (before : visited.IsPrefix source) :
    (Encoding.sequence codec visited).length ≤ (Encoding.sequence codec source).length := by
  obtain ⟨suffix,rfl⟩:=before
  simp only [Encoding.sequence_length,List.map_append,List.sum_append]
  omega

/-- Uniform bound for every partial reindexing accumulator, including its
list header. Prefix membership alone suffices; sources need not be sorted. -/
theorem reindexPrefix_encoded_polynomial (mapping : Array Nat)
    (visited source initial : List (Nat×Nat)) (before : visited.IsPrefix source) :
    ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode
      (visited.foldl (fun acc edge=>addCount (mapping[edge.1]?.getD 0) edge.2 acc) initial)).length ≤
      5*(((Encoding.array Encoding.natural).encode mapping).length+
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) source).length+
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) initial).length+1)^2 := by
  let A:=(Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) initial).length
  let B:=((Encoding.array Encoding.natural).encode mapping).length
  let C:=(Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) source).length
  let output:=visited.foldl (fun acc edge=>addCount (mapping[edge.1]?.getD 0) edge.2 acc) initial
  have prefixBits:=prefix_sequence_length (Encoding.product Encoding.natural Encoding.natural) visited source before
  have prefixCount:=(incoming_length_le_bits visited).trans prefixBits
  have initialCount:=incoming_length_le_bits initial
  have count:=reindex_length_le mapping visited initial
  have header : output.length.size ≤ output.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have payload:=reindex_encoded_length mapping visited initial B
    (fun edge _=>Encoding.naturalArray_entry_size_le mapping edge.1)
  have scaled:=Nat.mul_le_mul_right B (Nat.mul_le_mul_left 2 prefixCount)
  change visited.length ≤ C at prefixCount
  change initial.length ≤ A at initialCount
  change output.length ≤ initial.length+visited.length at count
  change (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) output).length ≤
    A+(Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) visited).length+
      2*visited.length*B at payload
  change (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) visited).length ≤ C at prefixBits
  change 2*visited.length*B ≤ 2*C*B at scaled
  change (Encoding.natural.encode output.length++
    Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) output).length ≤ 5*(B+C+A+1)^2
  simp only [List.length_append,Encoding.natural_length]
  nlinarith only [header,count,initialCount,prefixCount,payload,prefixBits,scaled,
    Nat.zero_le A,Nat.zero_le B,Nat.zero_le C]

end Counting.Executable
