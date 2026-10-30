import Counting.StackDagCanonicalCollectBounds

namespace Counting.StackMachine.DagUpdate.Canonical
set_option maxHeartbeats 2000000

private theorem collectEntries_payload_bound (mapping : Array Nat) (level index : Nat)
    (nodes : List Executable.Node) (cap : Nat) (positive : 1 ≤ cap)
    (mapBound : ((Encoding.array Encoding.natural).encode mapping).length ≤ cap)
    (indices : index+nodes.length ≤ cap)
    (nodeBound : ∀ node∈nodes,(Encoding.node.encode node).length ≤ cap) :
    (Encoding.sequence Sort.recordCodec (collectEntries mapping level index nodes)).length ≤
      nodes.length*(48*cap^2) := by
  induction nodes generalizing index with
  | nil => simp [collectEntries,Encoding.sequence]
  | cons node nodes ih =>
    have more := ih (index+1) (by simp only [List.length_cons] at indices;omega)
      (fun n member=>nodeBound n (by simp [member]))
    have remapped := Executable.referenceMap_encoded_polynomial mapping node
    have base : (Encoding.node.encode node).length+((Encoding.array Encoding.natural).encode mapping).length+1 ≤ 3*cap := by
      have := nodeBound node (by simp);omega
    have p2 := Nat.pow_le_pow_left base 2
    have output : (Encoding.node.encode (Executable.referenceMap mapping node)).length ≤ 45*cap^2 := by
      nlinarith only [remapped,p2]
    have indexBound : index ≤ cap := by omega
    have indexSize : index.size ≤ cap := (Nat.size_le.mpr Nat.lt_two_pow_self).trans indexBound
    have linear : cap ≤ cap^2 := Nat.le_self_pow (by decide) _
    have one : 1 ≤ cap^2 := one_le_pow₀ positive
    have record : (Sort.recordCodec.encode (index,Executable.referenceMap mapping node)).length ≤ 48*cap^2 := by
      simp only [Sort.recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
      omega
    by_cases selected : node.level=level
    · simp only [collectEntries,if_pos selected,Encoding.sequence,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [collectEntries,if_neg selected,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- The collector's output is a compact indexed record list. Reversing the
selection changes order but preserves its total encoding length. -/
theorem collectEntries_encoded_cap (mapping : Array Nat) (level index : Nat)
    (nodes : List Executable.Node) (cap : Nat) (positive : 1 ≤ cap)
    (sourceBound : ((Encoding.list Encoding.node).encode nodes).length ≤ cap)
    (mapBound : ((Encoding.array Encoding.natural).encode mapping).length ≤ cap)
    (indices : index+nodes.length ≤ cap) :
    ((Encoding.list Sort.recordCodec).encode (collectEntries mapping level index nodes).reverse).length ≤
      100*cap^3 := by
  have nodeBound (node : Executable.Node) (member : node∈nodes) : (Encoding.node.encode node).length ≤ cap := by
    have bound := Encoding.array_member_length_le Encoding.node nodes.toArray node (by simpa using member)
    simp only [Encoding.array,Encoding.transport] at bound
    exact bound.trans sourceBound
  have payload := collectEntries_payload_bound mapping level index nodes cap positive mapBound indices nodeBound
  have count := collectEntries_length_le mapping level index nodes
  have countBound : (collectEntries mapping level index nodes).length ≤ cap := by omega
  have countBits : (collectEntries mapping level index nodes).length.size ≤ cap :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans countBound
  have sizeBound : nodes.length ≤ cap := by omega
  have scaled := Nat.mul_le_mul_right (48*cap^2) sizeBound
  have power : cap*(48*cap^2)=48*cap^3 := by ring
  rw [power] at scaled
  have linear : cap ≤ cap^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ cap^3 := one_le_pow₀ positive
  simp only [Encoding.list_length,List.length_reverse,List.map_reverse,List.sum_reverse]
  rw [Encoding.sequence_length] at payload
  omega

end Counting.StackMachine.DagUpdate.Canonical
