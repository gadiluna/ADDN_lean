import Counting.DagImportPrefixBounds

namespace Counting.Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem canonical_mapping_set_bound (mapping : Array Nat) (index value bound : Nat)
    (old : ∀ i : Nat,mapping[i]?.getD 0 ≤ bound) (fresh : value ≤ bound) :
    ∀ i : Nat,(mapping.set! index value)[i]?.getD 0 ≤ bound := by
  intro i
  simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  split
  · split <;> simp_all
  · exact old i

theorem canonical_reference_encoded_bound (mapping : Array Nat) (node : Node) (width : Nat)
    (bounded : ∀ i : Nat,mapping[i]?.getD 0 ≤ width) :
    (Encoding.node.encode (referenceMap mapping node)).length ≤
      (2*width+3)*((Encoding.node.encode node).length+1) := by
  have sizes : ∀ i : Nat,(mapping[i]?.getD 0).size ≤ width := fun i=>
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (bounded i)
  have mapped := referenceMap_encoded_length mapping node width sizes
  have entries := incoming_length_le_bits node.incoming
  have count : node.incoming.length ≤ (Encoding.node.encode node).length := by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    rw [Encoding.sequence_length] at entries
    simp only [Encoding.product,List.length_append,Encoding.natural_length] at entries
    omega
  have product := Nat.mul_le_mul_left (2*width) (Nat.add_le_add_right count 1)
  nlinarith only [mapped,product,Nat.zero_le (Encoding.node.encode node).length]

theorem canonical_intern_payload_bound (pool : Array Node) (node : Node) :
    (Encoding.sequence Encoding.node (intern pool node).1.toList).length ≤
      (Encoding.sequence Encoding.node pool.toList).length+(Encoding.node.encode node).length := by
  unfold intern
  split
  · exact Nat.le_add_right _ _
  · simp only [Array.toList_push,Encoding.sequence_length,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,le_refl]

theorem canonicalInsertFold_bounds (source : Vista) (indices : List Nat) (state : CanonicalState)
    (width length : Nat) (capacity : state.1.size+indices.length ≤ width)
    (bounded : ∀ i : Nat,state.2[i]?.getD 0 ≤ width)
    (nodes : ∀ i∈indices,(Encoding.node.encode (source.node i)).length ≤ length) :
    let next := indices.foldl (canonicalInsert source) state
    next.1.size ≤ state.1.size+indices.length ∧
    next.2.size=state.2.size ∧
    (∀ i : Nat,next.2[i]?.getD 0 ≤ width) ∧
    (Encoding.sequence Encoding.node next.1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+indices.length*((2*width+3)*(length+1)) := by
  induction indices generalizing state with
  | nil =>
    exact ⟨by simp,rfl,bounded,by simp⟩
  | cons index indices ih =>
    let node := referenceMap state.2 (source.node index)
    let current := canonicalInsert source state index
    have size : current.1.size ≤ state.1.size+1 := intern_size_le_succ state.1 node
    have nextCapacity : current.1.size+indices.length ≤ width := by
      simp only [List.length_cons] at capacity
      omega
    have refInside : (intern state.1 node).2 < (intern state.1 node).1.size := intern_index_lt _ _
    have bound : ∀ i : Nat,current.2[i]?.getD 0 ≤ width := by
      apply canonical_mapping_set_bound _ _ _ _ bounded
      change (intern state.1 node).2 ≤ width
      change (intern state.1 node).1.size ≤ state.1.size+1 at size
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨more,mapSize,finalBound,payload⟩ := ih current nextCapacity bound
      (fun i member=>nodes i (by simp [member]))
    have mapped := (canonical_reference_encoded_bound state.2 (source.node index) width bounded).trans
      (Nat.mul_le_mul_left (2*width+3) (Nat.add_le_add_right (nodes index (by simp)) 1))
    have emitted := canonical_intern_payload_bound state.1 node
    dsimp only [node] at emitted
    have currentSize : current.2.size=state.2.size := by simp [current,canonicalInsert]
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨?_,mapSize.trans currentSize,finalBound,?_⟩
    · exact more.trans (by simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        Nat.add_le_add_right size indices.length)
    change (Encoding.sequence Encoding.node (indices.foldl (canonicalInsert source) current).1.toList).length ≤ _
    change (Encoding.sequence Encoding.node (intern state.1 (referenceMap state.2 (source.node index))).1.toList).length+
      indices.length*((2*width+3)*(length+1)) ≥
      (Encoding.sequence Encoding.node (indices.foldl (canonicalInsert source) current).1.toList).length at payload
    nlinarith only [payload,mapped,emitted]

theorem canonicalLevel_bounds (source : Vista) (state : CanonicalState) (level width length : Nat)
    (capacity : state.1.size+source.nodes.size ≤ width)
    (bounded : ∀ i : Nat,state.2[i]?.getD 0 ≤ width)
    (nodes : ∀ i, i < source.nodes.size → (Encoding.node.encode (source.node i)).length ≤ length) :
    let next := canonicalLevel source state level
    next.1.size ≤ state.1.size+source.nodes.size ∧
    next.2.size=state.2.size ∧
    (∀ i : Nat,next.2[i]?.getD 0 ≤ width) ∧
    (Encoding.sequence Encoding.node next.1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+source.nodes.size*((2*width+3)*(length+1)) := by
  let order := (levelNodes source level).mergeSort (fun i j=>
    lexLE (referenceMap state.2 (source.node i)).key (referenceMap state.2 (source.node j)).key)
  have count : order.length ≤ source.nodes.size := by
    simp only [order,List.length_mergeSort,levelNodes]
    exact (List.length_filter_le _ _).trans_eq List.length_range
  have inside : ∀ i∈order,i < source.nodes.size := by
    intro i member
    simp only [order,List.mem_mergeSort,levelNodes,List.mem_filter,List.mem_range] at member
    exact member.1
  obtain ⟨size,mapSize,mapping,payload⟩ := canonicalInsertFold_bounds source order state width length
    (by omega) bounded (fun i member=>nodes i (inside i member))
  refine ⟨size.trans (Nat.add_le_add_left count _),mapSize,mapping,?_⟩
  exact payload.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _)

def canonicalPrefix (source : Vista) (levels : Nat) : CanonicalState :=
  (List.range levels).foldl (canonicalLevel source) (#[],Array.replicate source.nodes.size 0)

theorem canonicalPrefix_bounds (source : Vista) (levels length : Nat) (steps : levels ≤ source.nodes.size)
    (nodes : ∀ i, i < source.nodes.size → (Encoding.node.encode (source.node i)).length ≤ length) :
    (canonicalPrefix source levels).1.size ≤ levels*source.nodes.size ∧
    (canonicalPrefix source levels).2.size=source.nodes.size ∧
    (∀ i : Nat,(canonicalPrefix source levels).2[i]?.getD 0 ≤ source.nodes.size^2) ∧
    (Encoding.sequence Encoding.node (canonicalPrefix source levels).1.toList).length ≤
      levels*source.nodes.size*((2*source.nodes.size^2+3)*(length+1)) := by
  induction levels with
  | zero =>
    simp only [canonicalPrefix,List.range_zero,List.foldl_nil,Array.size_empty,Array.size_replicate,
      Nat.zero_mul,Array.toList_empty,Encoding.sequence,List.length_nil,Nat.le_refl,true_and]
    refine ⟨?_,trivial⟩
    intro i
    simp only [Array.getElem?_replicate]
    split <;> simp
  | succ levels ih =>
    obtain ⟨count,mapSize,bounded,payload⟩ := ih (by omega)
    have capacity : (canonicalPrefix source levels).1.size+source.nodes.size ≤ source.nodes.size^2 := by
      nlinarith only [count,steps]
    obtain ⟨countNext,mapSizeNext,boundedNext,payloadNext⟩ :=
      canonicalLevel_bounds source (canonicalPrefix source levels) levels (source.nodes.size^2) length capacity bounded nodes
    have next : canonicalPrefix source (levels+1)=canonicalLevel source (canonicalPrefix source levels) levels := by
      simp [canonicalPrefix,List.range_succ]
    rw [next]
    refine ⟨by nlinarith only [countNext,count],mapSizeNext.trans mapSize,boundedNext,?_⟩
    nlinarith only [payloadNext,payload]

end Counting.Executable
