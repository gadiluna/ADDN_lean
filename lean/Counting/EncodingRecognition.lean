import Counting.EncodingRecognitionBounds
import Counting.RealizabilityKnowledge

/-! Complete serialized complementary witnesses for `AtMostOneVista`.
Both compatible orders and both compact arrays are included in the bound;
the bound is a cubic polynomial in the actual DAG-and-leader input length.
Machine running time for verifying these witnesses is a separate theorem. -/
namespace Counting.Encoding
open Executable

def orderWitness : Codec (Nat × List Nat) := product natural (list natural)
def twoOrderWitness : Codec ((Nat × List Nat) × (Nat × List Nat)) := product orderWitness orderWitness

theorem orderWitness_length (order : Nat) (counts : List Nat) :
    (orderWitness.encode (order, counts)).length =
      (2 * order.size + 1) + ((list natural).encode counts).length := by
  simp only [orderWitness, product, List.length_append, natural_length]

theorem orderWitness_bound (v : Vista) (weights : Array Nat) (ell order L : Nat)
    (accepted : RealizabilityVerifier.verify v weights ell order = true)
    (nodes : v.nodes.size ≤ L) (orderBits : order.size ≤ 2 * (L + 1) ^ 2 + 1) :
    (orderWitness.encode (order, weights.toList)).length ≤ 10 * (L + 1) ^ 3 := by
  have counts := natural_list_length_le weights.toList order (accepted_counts_le v weights ell order accepted)
  have size := ((RealizabilityVerifier.verify_iff_certificate v weights ell order).mp accepted).2.1
  simp only [Array.length_toList, size] at counts
  have header : v.nodes.size.size ≤ v.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have product := Nat.mul_le_mul nodes (show 2 * order.size + 1 ≤ 4 * (L + 1) ^ 2 + 3 by omega)
  rw [orderWitness_length]
  nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 2)]

theorem twoOrderWitness_length (first second : Nat × List Nat) :
    (twoOrderWitness.encode (first, second)).length =
      (orderWitness.encode first).length + (orderWitness.encode second).length := by
  simp only [twoOrderWitness, product, List.length_append]

/-- Both orders and both arrays are compact actual data accepted by the
executable verifier, rather than a hypothetical expanded network. -/
theorem vista_complement_encoded_witnesses (v : Vista) (valid : v.valid = true) (ell : Nat)
    (negative : ¬ Realizability.AtMostOneVista ell v.denotes) :
    ∃ first second : Nat, ∃ firstCounts secondCounts : Array Nat,
      first ≠ second ∧
      RealizabilityVerifier.verify v firstCounts ell first = true ∧
      RealizabilityVerifier.verify v secondCounts ell second = true ∧
      first.size ≤ 2 * ((vistaInput.encode (v, ell)).length + 1) ^ 2 + 1 ∧
      second.size ≤ 2 * ((vistaInput.encode (v, ell)).length + 1) ^ 2 + 1 ∧
      (twoOrderWitness.encode ((first, firstCounts.toList), (second, secondCounts.toList))).length ≤
        20 * ((vistaInput.encode (v, ell)).length + 1) ^ 3 := by
  obtain ⟨depth, nodes, labels⟩ := vistaInput_parameters v valid ell
  obtain ⟨first, second, k₁, k₂, different, cert₁, cert₂, bits₁, bits₂, _, _⟩ :=
    Realizability.vista_complement_polynomial_witnesses ell (v.node v.bottom).level v.denotes
      (vistaInput.encode (v, ell)).length depth nodes labels negative
  let firstCounts := RealizabilityVerifier.encodeCounts v k₁
  let secondCounts := RealizabilityVerifier.encodeCounts v k₂
  have accepted₁ : RealizabilityVerifier.verify v firstCounts ell first = true :=
    RealizabilityVerifier.verify_encodeCounts v valid ell first k₁ cert₁
  have accepted₂ : RealizabilityVerifier.verify v secondCounts ell second = true :=
    RealizabilityVerifier.verify_encodeCounts v valid ell second k₂ cert₂
  have stored : v.nodes.size ≤ (vistaInput.encode (v, ell)).length := by
    rw [vistaInput_length]
    exact (vista_nodes_le_length v).trans (Nat.le_add_right _ _)
  have bound₁ := orderWitness_bound v firstCounts ell first _ accepted₁ stored bits₁
  have bound₂ := orderWitness_bound v secondCounts ell second _ accepted₂ stored bits₂
  refine ⟨first, second, firstCounts, secondCounts, different, accepted₁, accepted₂, bits₁, bits₂, ?_⟩
  rw [twoOrderWitness_length]
  omega

theorem twoOrderWitness_sound (v : Vista) (ell first second : Nat) (firstCounts secondCounts : Array Nat)
    (different : first ≠ second)
    (accepted₁ : RealizabilityVerifier.verify v firstCounts ell first = true)
    (accepted₂ : RealizabilityVerifier.verify v secondCounts ell second = true) :
    ¬ Realizability.AtMostOneVista ell v.denotes :=
  (Realizability.not_atMostOne_iff_two ell v.denotes).mpr
    ⟨first, second, different, RealizabilityVerifier.verify_sound v firstCounts ell first accepted₁,
      RealizabilityVerifier.verify_sound v secondCounts ell second accepted₂⟩

def verifyTwoOrders (v : Vista) (ell : Nat) (witness : (Nat × List Nat) × (Nat × List Nat)) : Bool :=
  witness.1.1 != witness.2.1 &&
    RealizabilityVerifier.verify v witness.1.2.toArray ell witness.1.1 &&
    RealizabilityVerifier.verify v witness.2.2.toArray ell witness.2.1

theorem verifyTwoOrders_iff (v : Vista) (ell : Nat) (witness : (Nat × List Nat) × (Nat × List Nat)) :
    verifyTwoOrders v ell witness = true ↔
      witness.1.1 ≠ witness.2.1 ∧
      RealizabilityVerifier.verify v witness.1.2.toArray ell witness.1.1 = true ∧
      RealizabilityVerifier.verify v witness.2.2.toArray ell witness.2.1 = true := by
  simp only [verifyTwoOrders, Bool.and_eq_true, bne_iff_ne, and_assoc]

theorem verifyTwoOrders_sound (v : Vista) (ell : Nat) (witness : (Nat × List Nat) × (Nat × List Nat))
    (accepted : verifyTwoOrders v ell witness = true) :
    v.valid = true ∧ ¬ Realizability.AtMostOneVista ell v.denotes := by
  obtain ⟨different, first, second⟩ := (verifyTwoOrders_iff v ell witness).mp accepted
  exact ⟨((RealizabilityVerifier.verify_iff_certificate _ _ _ _).mp first).1,
    twoOrderWitness_sound _ _ _ _ _ _ different first second⟩

def binaryComplementVerifier (input witness : List Bool) : Bool :=
  match vistaInput.decodeExact input, twoOrderWitness.decodeExact witness with
  | some (v, ell), some certificate => verifyTwoOrders v ell certificate
  | _, _ => false

theorem binaryComplementVerifier_sound (input witness : List Bool)
    (accepted : binaryComplementVerifier input witness = true) :
    ∃ v ell, vistaInput.encode (v, ell) = input ∧ v.valid = true ∧
      ¬ Realizability.AtMostOneVista ell v.denotes := by
  unfold binaryComplementVerifier at accepted
  cases decoded : vistaInput.decodeExact input with
  | none => simp only [decoded, Bool.false_eq_true] at accepted
  | some pair =>
      rcases pair with ⟨v, ell⟩
      cases certificate : twoOrderWitness.decodeExact witness with
      | none => simp only [decoded, certificate, Bool.false_eq_true] at accepted
      | some value =>
          simp only [decoded, certificate] at accepted
          exact ⟨v, ell, (vistaInput.decodeExact_iff _ _).mp decoded,
            verifyTwoOrders_sound v ell value accepted⟩

theorem binaryComplementVerifier_complete (v : Vista) (valid : v.valid = true) (ell : Nat)
    (negative : ¬ Realizability.AtMostOneVista ell v.denotes) :
    ∃ witness : List Bool,
      binaryComplementVerifier (vistaInput.encode (v, ell)) witness = true ∧
      witness.length ≤ 20 * ((vistaInput.encode (v, ell)).length + 1) ^ 3 := by
  obtain ⟨first, second, firstCounts, secondCounts, different, accepted₁, accepted₂, _, _, bound⟩ :=
    vista_complement_encoded_witnesses v valid ell negative
  let certificate := ((first, firstCounts.toList), (second, secondCounts.toList))
  refine ⟨twoOrderWitness.encode certificate, ?_, bound⟩
  rw [binaryComplementVerifier,
    (vistaInput.decodeExact_iff _ _).mpr rfl, (twoOrderWitness.decodeExact_iff _ _).mpr rfl]
  apply (verifyTwoOrders_iff v ell certificate).mpr
  exact ⟨different, by simpa only [certificate, Array.toArray_toList] using accepted₁,
    by simpa only [certificate, Array.toArray_toList] using accepted₂⟩

/-- The empty-spectrum convention also covers malformed serialized input,
not just invalid DAGs that successfully parse. -/
noncomputable def binaryVistaSpectrum (input : List Bool) : Set Nat :=
  match vistaInput.decodeExact input with
  | none => ∅
  | some (v, ell) => Realizability.encodedSpectrum ell v

def BinaryAtMostOneVista (input : List Bool) : Prop := (binaryVistaSpectrum input).Subsingleton

theorem encodedSpectrum_not_unique (v : Vista) (ell : Nat) :
    ¬ (Realizability.encodedSpectrum ell v).Subsingleton ↔
      v.valid = true ∧ ¬ Realizability.AtMostOneVista ell v.denotes := by
  by_cases valid : v.valid = true
  · rw [Realizability.encodedSpectrum_valid ell v valid]
    simp only [Realizability.AtMostOneVista, valid, true_and]
  · rw [Realizability.encodedSpectrum_invalid ell v (Bool.eq_false_iff.mpr valid)]
    simp only [Set.subsingleton_empty, not_true_eq_false, valid, Bool.false_eq_true, false_and]

theorem binaryComplementVerifier_sound_unique (input witness : List Bool)
    (accepted : binaryComplementVerifier input witness = true) : ¬ BinaryAtMostOneVista input := by
  obtain ⟨v, ell, same, valid, negative⟩ := binaryComplementVerifier_sound input witness accepted
  subst input
  change ¬ (binaryVistaSpectrum (vistaInput.encode (v, ell))).Subsingleton
  rw [binaryVistaSpectrum, (vistaInput.decodeExact_iff _ _).mpr rfl]
  exact (encodedSpectrum_not_unique v ell).mpr ⟨valid, negative⟩

/-- The exact complementary witness relation on arbitrary binary inputs,
including invalid encodings. This is the certificate-size/functional part
of coNP membership; it deliberately makes no machine-time assertion. -/
theorem binaryVista_complement_iff (input : List Bool) :
    ¬ BinaryAtMostOneVista input ↔ ∃ witness : List Bool,
      witness.length ≤ 20 * (input.length + 1) ^ 3 ∧
      binaryComplementVerifier input witness = true := by
  constructor
  · intro negative
    unfold BinaryAtMostOneVista binaryVistaSpectrum at negative
    cases decoded : vistaInput.decodeExact input with
    | none => simp only [decoded, Set.subsingleton_empty, not_true_eq_false] at negative
    | some pair =>
        rcases pair with ⟨v, ell⟩
        simp only [decoded] at negative
        obtain ⟨valid, multiple⟩ := (encodedSpectrum_not_unique v ell).mp negative
        obtain ⟨witness, accepted, bound⟩ := binaryComplementVerifier_complete v valid ell multiple
        have same := (vistaInput.decodeExact_iff _ _).mp decoded
        rw [same] at accepted bound
        exact ⟨witness, bound, accepted⟩
  · rintro ⟨witness, _, accepted⟩
    exact binaryComplementVerifier_sound_unique input witness accepted

end Counting.Encoding
