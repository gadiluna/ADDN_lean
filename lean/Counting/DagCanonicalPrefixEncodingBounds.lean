import Counting.DagCanonicalPrefixBounds

namespace Counting.Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem canonical_source_node_bound (source : Vista) (index : Nat) (inside : index < source.nodes.size) :
    (Encoding.node.encode (source.node index)).length ≤ (Encoding.vista.encode source).length := by
  have member : source.node index∈source.nodes.toList := by
    apply List.mem_iff_getElem.mpr
    exact ⟨index,by simpa using inside,by simp [Vista.node,inside]⟩
  have bound := Encoding.array_member_length_le Encoding.node source.nodes (source.node index) member
  simp only [Encoding.array,Encoding.transport] at bound
  simp only [Encoding.vista,Encoding.transport,Encoding.product,List.length_append]
  omega

theorem canonical_source_count_bound (source : Vista) : source.nodes.size ≤ (Encoding.vista.encode source).length := by
  have bound := Encoding.array_size_le_length Encoding.node source.nodes (fun node _=>Encoding.node_positive_length node)
  simp only [Encoding.array,Encoding.transport] at bound
  simp only [Encoding.vista,Encoding.transport,Encoding.product,List.length_append]
  omega

/-- Every outer canonicalization state has polynomial compact size. The
bound allows up to one complete level pass per explicit source node and
does not require the source's graph-validity invariant. -/
theorem canonicalPrefix_encoded_polynomial (source : Vista) (levels : Nat) (steps : levels ≤ source.nodes.size) :
    let state := canonicalPrefix source levels
    ((Encoding.array Encoding.node).encode state.1).length ≤ 100*((Encoding.vista.encode source).length+1)^5 ∧
    ((Encoding.array Encoding.natural).encode state.2).length ≤ 100*((Encoding.vista.encode source).length+1)^5 ∧
    state.2.size=source.nodes.size := by
  let L := (Encoding.vista.encode source).length
  let K := L+1
  let n := source.nodes.size
  let state := canonicalPrefix source levels
  have positive : 1 ≤ K := by dsimp [K];omega
  have nBound : n ≤ K := (canonical_source_count_bound source).trans (by dsimp [K,L];omega)
  have levelsBound : levels ≤ K := steps.trans nBound
  obtain ⟨count,mapSize,bounded,payload⟩ := canonicalPrefix_bounds source levels L steps
    (canonical_source_node_bound source)
  have nSquared := Nat.pow_le_pow_left nBound 2
  have width : source.nodes.size^2 ≤ K^2 := nSquared
  have levelsProduct : levels*n ≤ K^2 := by
    simpa only [pow_two] using Nat.mul_le_mul levelsBound nBound
  have stateCount : state.1.size ≤ K^2 := count.trans levelsProduct
  have header : state.1.size.size ≤ K^2 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans stateCount
  have squarePositive : 1 ≤ K^2 := one_le_pow₀ positive
  have fivePositive : 1 ≤ K^5 := one_le_pow₀ positive
  have squareFive : K^2 ≤ K^5 := Nat.pow_le_pow_right positive (by decide)
  have linearFive : K ≤ K^5 := Nat.le_self_pow (by decide) _
  have factor : 2*source.nodes.size^2+3 ≤ 5*K^2 := by omega
  have scaled := Nat.mul_le_mul levelsProduct (Nat.mul_le_mul_right K factor)
  have payloadBound : (Encoding.sequence Encoding.node state.1.toList).length ≤ 5*K^5 := by
    change levels*n*((2*source.nodes.size^2+3)*K) ≤ K^2*(5*K^2*K) at scaled
    have identity : K^2*(5*K^2*K)=5*K^5 := by ring
    rw [identity] at scaled
    exact payload.trans scaled
  have mapMember : ∀ value∈state.2.toList,value ≤ source.nodes.size^2 := by
    intro value member
    obtain ⟨i,inside,equal⟩ := List.mem_iff_getElem.mp member
    have insideArray : i < state.2.size := by simpa only [Array.length_toList] using inside
    have bound := bounded i
    change state.2[i]?.getD 0 ≤ source.nodes.size^2 at bound
    rw [Array.getElem?_eq_getElem insideArray,Option.getD_some] at bound
    simpa only [←equal,Array.getElem_toList] using bound
  have mapping := Encoding.natural_list_length_le state.2.toList (source.nodes.size^2) mapMember
  have widthBits : (source.nodes.size^2).size ≤ K^2 := (Nat.size_le.mpr Nat.lt_two_pow_self).trans width
  have nBits : source.nodes.size.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans nBound
  change n.size ≤ K at nBits
  have mapProduct := Nat.mul_le_mul nBound (show 2*(source.nodes.size^2).size+1 ≤ 3*K^2 by omega)
  have cubicFive : K^3 ≤ K^5 := Nat.pow_le_pow_right positive (by decide)
  have mapCost : n*(2*(source.nodes.size^2).size+1) ≤ 3*K^5 := by
    calc
      _ ≤ K*(3*K^2) := mapProduct
      _ = 3*K^3 := by ring
      _ ≤ 3*K^5 := Nat.mul_le_mul_left 3 cubicFive
  change ((Encoding.array Encoding.node).encode state.1).length ≤ 100*K^5 ∧
    ((Encoding.array Encoding.natural).encode state.2).length ≤ 100*K^5 ∧ state.2.size=n
  refine ⟨?_,?_,mapSize⟩
  · rw [Encoding.array_length,←Encoding.sequence_length]
    omega
  · change ((Encoding.list Encoding.natural).encode state.2.toList).length ≤ 100*K^5
    simp only [Array.length_toList] at mapping
    change state.2.size=n at mapSize
    rw [mapSize] at mapping
    omega

end Counting.Executable
