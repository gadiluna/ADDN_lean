import Counting.DagReferenceEncodingBounds
import Counting.DagUpdateSizeBounds
import Counting.EncodingVerifier

namespace Counting.Executable
set_option backward.isDefEq.respectTransparency false

/-- The actual import transition, with its accumulated reference table. -/
def importStep (state : Array Node × Array Nat) (node : Node) : Array Node × Array Nat :=
  let next := intern state.1 (referenceMap state.2 node)
  (next.1,state.2.push next.2)

private theorem push_lookup_le (mapping : Array Nat) (value bound : Nat)
    (old : ∀ (i : Nat), mapping[i]?.getD 0  ≤  bound) (new : value  ≤  bound) :
    ∀ (i : Nat), (mapping.push value)[i]?.getD 0  ≤  bound := by
  intro i
  by_cases inside : i < mapping.size
  · simpa only [Array.getElem?_push_lt inside,Array.getElem?_eq_getElem inside] using old i
  · by_cases last : i=mapping.size
    · subst i
      simpa only [Array.getElem?_push_size,Option.getD_some] using new
    · have outside : (mapping.push value).size ≤ i := by simp only [Array.size_push];omega
      simp only [Array.getElem?_eq_none outside,Option.getD_none]
      exact Nat.zero_le _

private theorem incoming_le_node_bits (node : Node) :
    node.incoming.length  ≤  (Encoding.node.encode node).length := by
  have entries:=incoming_length_le_bits node.incoming
  rw [Encoding.node_length]
  unfold Encoding.nodeBits
  rw [Encoding.sequence_length] at entries
  simp only [Encoding.product,List.length_append,Encoding.natural_length] at entries
  omega

private theorem referenceMap_uniform (mapping : Array Nat) (node : Node) (width : Nat)
    (bounded : ∀ (i : Nat),mapping[i]?.getD 0 ≤ width) :
    (Encoding.node.encode (referenceMap mapping node)).length  ≤ 
      (2*width+3)*((Encoding.node.encode node).length+1) := by
  have lengths : ∀ (i : Nat),(mapping[i]?.getD 0).size ≤ width := by
    intro i
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (bounded i)
  have mapped:=referenceMap_encoded_length mapping node width lengths
  have entries:=incoming_le_node_bits node
  have product:=Nat.mul_le_mul_left (2*width) (Nat.add_le_add_right entries 1)
  nlinarith only [mapped,product,Nat.zero_le (Encoding.node.encode node).length]

private theorem intern_payload_le (pool : Array Node) (node : Node) :
    (Encoding.sequence Encoding.node (intern pool node).1.toList).length  ≤ 
      (Encoding.sequence Encoding.node pool.toList).length+(Encoding.node.encode node).length := by
  unfold intern
  split
  · exact Nat.le_add_right _ _
  · simp only [Array.toList_push,Encoding.sequence_length,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,le_refl]

/-- A uniform cap on mapping values suffices for an additive bound over
the complete fold. No graph-validity or topological-order premise is used. -/
theorem importFold_payload_bound (nodes : List Node) (state : Array Node × Array Nat) (width : Nat)
    (capacity : state.1.size+nodes.length ≤ width)
    (bounded : ∀ (i : Nat),state.2[i]?.getD 0 ≤ width) :
    (Encoding.sequence Encoding.node (nodes.foldl importStep state).1.toList).length  ≤ 
      (Encoding.sequence Encoding.node state.1.toList).length+
        (2*width+3)*((Encoding.sequence Encoding.node nodes).length+nodes.length) ∧
    (∀ (i : Nat),(nodes.foldl importStep state).2[i]?.getD 0 ≤ width) := by
  induction nodes generalizing state with
  | nil => simpa only [List.foldl_nil,Encoding.sequence,List.length_nil,Nat.add_zero,Nat.mul_zero]
      using And.intro (Nat.le_refl _) bounded
  | cons node nodes ih =>
    have size:=intern_size_le_succ state.1 (referenceMap state.2 node)
    have capacityNext : (importStep state node).1.size+nodes.length ≤ width := by
      change (intern state.1 (referenceMap state.2 node)).1.size+nodes.length ≤ width
      simp only [List.length_cons] at capacity
      omega
    have index:=intern_index_lt state.1 (referenceMap state.2 node)
    have nextBound : ∀ (i : Nat),(importStep state node).2[i]?.getD 0 ≤ width := by
      apply push_lookup_le _ _ _ bounded
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨remaining,finalBound⟩:=ih (importStep state node) capacityNext nextBound
    have mapped:=referenceMap_uniform state.2 node width bounded
    have first:=intern_payload_le state.1 (referenceMap state.2 node)
    refine ⟨?_,finalBound⟩
    simp only [List.foldl_cons,Encoding.sequence,List.length_append,List.length_cons]
    change (Encoding.sequence Encoding.node (nodes.foldl importStep (importStep state node)).1.toList).length ≤ 
      (Encoding.sequence Encoding.node (intern state.1 (referenceMap state.2 node)).1.toList).length+
        (2*width+3)*((Encoding.sequence Encoding.node nodes).length+nodes.length) at remaining
    nlinarith only [remaining,mapped,first]

theorem importFold_mapping_size (nodes : List Node) (state : Array Node × Array Nat) :
    (nodes.foldl importStep state).2.size=state.2.size+nodes.length := by
  induction nodes generalizing state with
  | nil => simp
  | cons node nodes ih =>
    simp only [List.foldl_cons,ih,importStep,Array.size_push,List.length_cons]
    omega

/-- Every intermediate import state has a quadratic bound in the original
serialized pool and explicit source list. Sharing is retained throughout. -/
theorem importFold_encoded_polynomial (pool : Array Node) (nodes : List Node) :
    ((Encoding.array Encoding.node).encode (nodes.foldl importStep (pool,#[])).1).length  ≤ 
      20*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+1)^2 ∧
    ((Encoding.array Encoding.natural).encode (nodes.foldl importStep (pool,#[])).2).length  ≤ 
      10*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+1)^2 := by
  let state:=nodes.foldl importStep (pool,#[])
  let P:=((Encoding.array Encoding.node).encode pool).length
  let S:=((Encoding.list Encoding.node).encode nodes).length
  let K:=P+S+1
  let width:=pool.size+nodes.length
  have poolCount : pool.size ≤ P := Encoding.array_size_le_length _ _
    (fun node _=>Encoding.node_positive_length node)
  have sourceCount : nodes.length ≤ S := by
    have count:=Encoding.node_sequence_length nodes
    dsimp only [S]
    rw [Encoding.list_length]
    simpa only [Encoding.node_length] using count.trans (Nat.le_add_left _ _)
  have sourcePayload : (Encoding.sequence Encoding.node nodes).length ≤ S := by
    dsimp only [S]
    simp only [Encoding.list,List.length_append]
    omega
  have poolPayload : (Encoding.sequence Encoding.node pool.toList).length ≤ P := by
    dsimp only [P]
    simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append]
    omega
  have widthK : width ≤ K := by dsimp only [width,K];omega
  have ⟨payload,mapping⟩:=importFold_payload_bound nodes (pool,#[]) width le_rfl (by simp)
  have count : state.1.size ≤ width := importFold_size_le nodes (pool,#[])
  have header : state.1.size.size ≤ width :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans count
  have mapCount : state.2.size=nodes.length := by
    simpa only [Array.size_empty,Nat.zero_add] using importFold_mapping_size nodes (pool,#[])
  have mapMember : ∀ value∈state.2.toList,value ≤ width := by
    intro value member
    obtain ⟨i,inside,equal⟩:=List.mem_iff_getElem.mp member
    have insideArray : i < state.2.size := by simpa only [Array.length_toList] using inside
    have bound:=mapping i
    change state.2[i]?.getD 0 ≤ width at bound
    rw [Array.getElem?_eq_getElem insideArray,Option.getD_some] at bound
    simpa only [←equal,Array.getElem_toList] using bound
  have mapLength:=Encoding.natural_list_length_le state.2.toList width mapMember
  have widthBits : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  have sourceBits : nodes.length.size ≤ nodes.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have payloadProduct:=Nat.mul_le_mul (show 2*width+3 ≤ 2*K+3 by omega)
    (show (Encoding.sequence Encoding.node nodes).length+nodes.length ≤ 2*K by omega)
  have mappingProduct:=Nat.mul_le_mul (show nodes.length ≤ K by omega)
    (show 2*width.size+1 ≤ 2*K+1 by omega)
  have positive : 1 ≤ K := by dsimp only [K];omega
  constructor
  · change ((Encoding.array Encoding.node).encode state.1).length ≤ 20*K^2
    rw [Encoding.array_length,←Encoding.sequence_length]
    change (Encoding.sequence Encoding.node state.1.toList).length ≤ 
      (Encoding.sequence Encoding.node pool.toList).length+
        (2*width+3)*((Encoding.sequence Encoding.node nodes).length+nodes.length) at payload
    have pK : P ≤ K := by dsimp only [K];omega
    nlinarith only [header,widthK,payloadProduct,payload,poolPayload,positive,pK]
  · change ((Encoding.list Encoding.natural).encode state.2.toList).length ≤ 10*K^2
    simp only [Array.length_toList,mapCount] at mapLength
    have sourceK : nodes.length ≤ K := by dsimp only [K];omega
    nlinarith only [mapLength,sourceBits,sourceK,mappingProduct,positive]

private theorem sequence_take_length_le {α : Type} (codec : Encoding.Codec α)
    (nodes : List α) (count : Nat) :
    (Encoding.sequence codec (nodes.take count)).length≤(Encoding.sequence codec nodes).length := by
  induction nodes generalizing count with
  | nil => simp [Encoding.sequence]
  | cons node nodes ih =>
    cases count with
    | zero => simp [Encoding.sequence]
    | succ count =>
      simpa only [List.take_succ_cons,Encoding.sequence,List.length_append] using
        Nat.add_le_add_left (ih count) (codec.encode node).length

private theorem list_take_length_le {α : Type} (codec : Encoding.Codec α)
    (nodes : List α) (count : Nat) :
    ((Encoding.list codec).encode (nodes.take count)).length≤((Encoding.list codec).encode nodes).length := by
  have payload:=sequence_take_length_le codec nodes count
  have takeCount : (nodes.take count).length ≤ nodes.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  have header:=Nat.size_le_size takeCount
  simp only [Encoding.list,List.length_append,Encoding.natural_length]
  omega

def importPrefixState (pool : Array Node) (nodes : List Node) (count : Nat) : Array Node × Array Nat :=
  (nodes.take count).foldl importStep (pool,#[])

/-- A single bound controls every prefix of the real import fold, including
the array headers. It is independent of the number of completed steps. -/
theorem importPrefix_encoded_polynomial (pool : Array Node) (nodes : List Node) (count : Nat) :
    ((Encoding.array Encoding.node).encode (importPrefixState pool nodes count).1).length ≤
      20*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+1)^2 ∧
    ((Encoding.array Encoding.natural).encode (importPrefixState pool nodes count).2).length ≤
      10*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+1)^2 := by
  have bounded:=importFold_encoded_polynomial pool (nodes.take count)
  have taken:=list_take_length_le Encoding.node nodes count
  have base := Nat.add_le_add_right
    (Nat.add_le_add_left taken ((Encoding.array Encoding.node).encode pool).length) 1
  have power:=Nat.pow_le_pow_left base 2
  exact ⟨bounded.1.trans (Nat.mul_le_mul_left 20 power),
    bounded.2.trans (Nat.mul_le_mul_left 10 power)⟩

theorem importVista_encoded_polynomial (pool : Array Node) (source : Vista) :
    ((Encoding.array Encoding.node).encode (importVista pool source).1).length ≤
      20*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.array Encoding.node).encode source.nodes).length+1)^2 ∧
    ((Encoding.array Encoding.natural).encode (importVista pool source).2).length ≤
      10*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.array Encoding.node).encode source.nodes).length+1)^2 := by
  have equation : importVista pool source=source.nodes.toList.foldl importStep (pool,#[]) := by
    simp only [importVista,←Array.foldl_toList]
    rfl
  rw [equation]
  exact importFold_encoded_polynomial pool source.nodes.toList

end Counting.Executable
