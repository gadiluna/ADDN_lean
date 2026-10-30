import Counting.EncodingVerifier
import Counting.RealizabilityRecognitionBits

/-! Relating the intrinsic vista parameters in the small-order theorem
to the actual binary encoding, including sparse multiplicity fields. -/
namespace Counting.Encoding
open Executable TimingProtocolLocal
open scoped BigOperators

def vistaInput : Codec (Vista × Nat) := product vista natural

theorem vistaInput_length (v : Vista) (ell : Nat) :
    (vistaInput.encode (v, ell)).length = (vista.encode v).length + (2 * ell.size + 1) := by
  simp only [vistaInput, product, List.length_append, natural_length]

theorem levelNodes_length_card (v : Vista) (r : Nat) :
    (levelNodes v r).length = ((Finset.range v.nodes.size).filter (fun i => (v.node i).level = r)).card := by
  have equal : (levelNodes v r).toFinset =
      (Finset.range v.nodes.size).filter (fun i => (v.node i).level = r) := by
    ext i
    simp only [List.mem_toFinset, mem_levelNodes, Finset.mem_filter, Finset.mem_range]
  rw [← equal, List.toFinset_card_of_nodup (levelNodes_nodup v r)]

theorem decoded_nodeCount_le (v : Vista) (valid : v.valid = true) :
    Realizability.nodeCount (v.node v.bottom).level v.denotes ≤ v.nodes.size := by
  unfold Realizability.nodeCount
  simp_rw [← levelNodes_length_eq_visible_card v valid, levelNodes_length_card]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

theorem nodeBits_le_vista (v : Vista) (i : Nat) (inside : i < v.nodes.size) :
    nodeBits (v.node i) ≤ (vista.encode v).length := by
  have member : v.node i ∈ v.nodes.toList := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i, by simpa only [Array.length_toList] using inside, ?_⟩
    simp only [Array.getElem_toList inside, Vista.node, Array.getElem?_eq_getElem inside, Option.getD_some]
  have bound : nodeBits (v.node i) ≤ (v.nodes.toList.map nodeBits).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨v.node i, member, rfl⟩)
  rw [vista_length]
  omega

theorem degreeBits_le_node (n : Node) : n.degree.size ≤ nodeBits n := by
  unfold nodeBits
  omega

theorem redBits_le_node (n : Node) (source : Nat) : (countFrom n source).size ≤ nodeBits n := by
  unfold countFrom
  cases found : n.incoming.find? (fun edge => edge.1 == source) with
  | none => simp only [Option.map_none, Option.getD_none, Nat.size_zero]; exact Nat.zero_le _
  | some edge =>
      have member := List.mem_of_find?_eq_some found
      have bound : (2 * edge.1.size + 1) + (2 * edge.2.size + 1) ≤
          (n.incoming.map (fun edge => (2 * edge.1.size + 1) + (2 * edge.2.size + 1))).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨edge, member, rfl⟩)
      simp only [Option.map_some, Option.getD_some]
      unfold nodeBits
      omega

theorem decoded_degreeBits_le (v : Vista) (valid : v.valid = true) (r : Nat)
    (H : Counting.FullHistory (r + 1))
    (visible : H ∈ levels (v.node v.bottom).level v.denotes (r + 1)) :
    (degree r H).size ≤ (vista.encode v).length := by
  rw [← decodedLevel_eq_levels v valid] at visible
  obtain ⟨i, inside, _, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
  rw [degree_decode]
  exact (degreeBits_le_node _).trans (nodeBits_le_vista v i inside)

theorem decoded_redBits_le (v : Vista) (valid : v.valid = true) (r : Nat)
    (old : Counting.FullHistory r) (new : Counting.FullHistory (r + 1))
    (oldVisible : old ∈ levels (v.node v.bottom).level v.denotes r)
    (newVisible : new ∈ levels (v.node v.bottom).level v.denotes (r + 1)) :
    (red r old new).size ≤ (vista.encode v).length := by
  rw [← decodedLevel_eq_levels v valid] at oldVisible newVisible
  obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp oldVisible
  obtain ⟨j, jinside, jlevel, rfl⟩ := (mem_decodedLevel _ _ _).mp newVisible
  rw [red_decode v valid r i j inside jinside level jlevel]
  exact (redBits_le_node _ _).trans (nodeBits_le_vista v j jinside)

theorem decoded_maxLabel_bits_le (v : Vista) (valid : v.valid = true) (ell : Nat) :
    (Realizability.maxLabel ell (v.node v.bottom).level v.denotes).size ≤
      (vistaInput.encode (v, ell)).length := by
  let L := (vistaInput.encode (v, ell)).length
  have vistaBound : (vista.encode v).length ≤ L := by dsimp [L]; rw [vistaInput_length]; omega
  have ellBound : ell.size ≤ L := by dsimp [L]; rw [vistaInput_length]; omega
  apply Nat.size_le.mpr
  unfold Realizability.maxLabel
  apply max_lt_iff.mpr
  refine ⟨Nat.size_le.mp ellBound, max_lt_iff.mpr ⟨?_, ?_⟩⟩
  · unfold Realizability.maxRed
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro r _
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro old oldVisible
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro new newVisible
    exact Nat.size_le.mp ((decoded_redBits_le v valid r old new oldVisible newVisible).trans vistaBound)
  · unfold Realizability.maxDegree
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro r _
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro H visible
    exact Nat.size_le.mp ((decoded_degreeBits_le v valid r H visible).trans vistaBound)

theorem vistaInput_parameters (v : Vista) (valid : v.valid = true) (ell : Nat) :
    (v.node v.bottom).level ≤ (vistaInput.encode (v, ell)).length ∧
    Realizability.nodeCount (v.node v.bottom).level v.denotes ≤ (vistaInput.encode (v, ell)).length ∧
    (Realizability.maxLabel ell (v.node v.bottom).level v.denotes).size ≤
      (vistaInput.encode (v, ell)).length := by
  have nodes : v.nodes.size ≤ (vistaInput.encode (v, ell)).length := by
    rw [vistaInput_length]
    exact (vista_nodes_le_length v).trans (Nat.le_add_right _ _)
  exact ⟨(RealizabilityVerifier.valid_depth_lt_size v valid).le.trans nodes,
    (decoded_nodeCount_le v valid).trans nodes, decoded_maxLabel_bits_le v valid ell⟩

theorem supportBound_bits_encoded (v : Vista) (valid : v.valid = true) (ell : Nat) :
    (Realizability.supportBound ell (v.node v.bottom).level v.denotes).size ≤
      2 * ((vistaInput.encode (v, ell)).length + 1) ^ 2 + 1 := by
  obtain ⟨depth, nodes, labels⟩ := vistaInput_parameters v valid ell
  exact SupportBitLength.support_power_size_polynomial _ _ _ _ depth nodes labels

theorem compatible_threshold_bits_encoded (v : Vista) (valid : v.valid = true) (ell : Nat) :
    (Realizability.supportBound ell (v.node v.bottom).level v.denotes + ell + 2).size ≤
      2 * ((vistaInput.encode (v, ell)).length + 1) ^ 2 + 1 := by
  obtain ⟨depth, nodes, labels⟩ := vistaInput_parameters v valid ell
  apply SupportBitLength.compatible_order_size_polynomial_of_leaders_le_max _ _ _ _ _
    depth nodes labels
  exact Nat.le_max_left _ _

end Counting.Encoding
