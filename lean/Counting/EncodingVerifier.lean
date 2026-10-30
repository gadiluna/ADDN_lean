import Counting.EncodingDag
import Counting.RealizabilityVerifierBounds

/-! Explicit bit lengths for the compact fixed-order certificate. This
module proves the size of the serialized witness, including framing and
array length. It does not assert a running-time bound for the verifier. -/
namespace Counting.Encoding

def fixedOrderInput : Codec (Executable.Vista × Nat × Nat) :=
  product vista (product natural natural)

theorem node_positive_length (n : Executable.Node) : 1 ≤ (node.encode n).length := by
  rw [node_length]
  unfold nodeBits
  omega

theorem node_sequence_length (nodes : List Executable.Node) :
    nodes.length ≤ (nodes.map nodeBits).sum := by
  induction nodes with
  | nil => rfl
  | cons head tail ih =>
      have positive := node_positive_length head
      rw [node_length] at positive
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

theorem vista_nodes_le_length (v : Executable.Vista) : v.nodes.size ≤ (vista.encode v).length := by
  have bound := node_sequence_length v.nodes.toList
  rw [Array.length_toList] at bound
  rw [vista_length]
  omega

theorem fixedOrderInput_length (v : Executable.Vista) (ell order : Nat) :
    (fixedOrderInput.encode (v, ell, order)).length = (vista.encode v).length +
      (2 * ell.size + 1) + (2 * order.size + 1) := by
  simp only [fixedOrderInput, product, List.length_append, natural_length]
  omega

theorem fixedOrderInput_nodes_le (v : Executable.Vista) (ell order : Nat) :
    v.nodes.size ≤ (fixedOrderInput.encode (v, ell, order)).length := by
  have := vista_nodes_le_length v
  rw [fixedOrderInput_length]
  omega

theorem fixedOrderInput_orderBits_le (v : Executable.Vista) (ell order : Nat) :
    order.size ≤ (fixedOrderInput.encode (v, ell, order)).length := by
  rw [fixedOrderInput_length]
  omega

theorem accepted_counts_le (v : Executable.Vista) (weights : Array Nat) (ell order : Nat)
    (accepted : RealizabilityVerifier.verify v weights ell order = true) :
    ∀ count ∈ weights.toList, count ≤ order := by
  intro count member
  obtain ⟨i, inside, equal⟩ := List.mem_iff_getElem.mp member
  have inArray : i < weights.size := by simpa only [Array.length_toList] using inside
  have size := ((RealizabilityVerifier.verify_iff_certificate v weights ell order).mp accepted).2.1
  have bound := RealizabilityVerifier.accepted_weight_le_order v weights ell order accepted i (by
    simpa only [size] using inArray)
  simp only [RealizabilityVerifier.weight, Array.getElem?_eq_getElem inArray, Option.getD_some] at bound
  rw [Array.getElem_toList inArray] at equal
  exact equal ▸ bound

theorem accepted_counts_encoded_linear (v : Executable.Vista) (weights : Array Nat) (ell order : Nat)
    (accepted : RealizabilityVerifier.verify v weights ell order = true) :
    ((list natural).encode weights.toList).length ≤ 5 * v.nodes.size * (order.size + 1) + 1 := by
  have bound := natural_list_length_le weights.toList order (accepted_counts_le v weights ell order accepted)
  have size := ((RealizabilityVerifier.verify_iff_certificate v weights ell order).mp accepted).2.1
  have header : v.nodes.size.size ≤ v.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [Array.length_toList, size] at bound
  nlinarith

/-- Polynomial witness length in the *binary input length*, with no
assumption that the proposed order is numerically small. -/
theorem accepted_counts_encoded_bound (v : Executable.Vista) (weights : Array Nat) (ell order : Nat)
    (accepted : RealizabilityVerifier.verify v weights ell order = true) :
    ((list natural).encode weights.toList).length ≤
      3 * ((fixedOrderInput.encode (v, ell, order)).length + 1) ^ 2 := by
  have payload := natural_list_length_le weights.toList order (accepted_counts_le v weights ell order accepted)
  have count := ((RealizabilityVerifier.verify_iff_certificate v weights ell order).mp accepted).2.1
  have nodes := fixedOrderInput_nodes_le v ell order
  have orderBits := fixedOrderInput_orderBits_le v ell order
  have header : v.nodes.size.size ≤ v.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [Array.length_toList, count] at payload
  nlinarith [Nat.mul_le_mul nodes (show 2 * order.size + 1 ≤
    2 * (fixedOrderInput.encode (v, ell, order)).length + 1 by omega)]

theorem exists_encoded_bounded_certificate (v : Executable.Vista) (valid : v.valid = true)
    (ell order : Nat) (realizable : Realizability.Realizable ell order v.denotes) :
    ∃ weights : Array Nat, RealizabilityVerifier.verify v weights ell order = true ∧
      ((list natural).encode weights.toList).length ≤
        3 * ((fixedOrderInput.encode (v, ell, order)).length + 1) ^ 2 := by
  obtain ⟨weights, accepted⟩ := (RealizabilityVerifier.exists_verified_iff v ell order).mpr ⟨valid, realizable⟩
  exact ⟨weights, accepted, accepted_counts_encoded_bound v weights ell order accepted⟩

end Counting.Encoding
