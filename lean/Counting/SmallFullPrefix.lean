import Counting.SmallPrefixTable

namespace Counting.SmallPrefix
open DirectedCounting TimingProtocolLocal
variable {A : Type} [Fintype A]

theorem fullLevel_card (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat) :
    (fullLevel G leader r).card = Fintype.card (PaperHistory.Node G leader r) := by
  classical
  have eq : fullLevel G leader r = Finset.univ.image (nodeHistory G leader r) := by
    ext h
    constructor
    · intro member
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_image.mpr ⟨PaperHistory.classOf G leader r a, Finset.mem_univ _,
        nodeHistory_classOf G leader r a⟩
    · intro member
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_image.mpr ⟨c.out, Finset.mem_univ _, rfl⟩
  rw [eq, Finset.card_image_of_injective _ (nodeHistory_injective G leader r), Finset.card_univ]

theorem anonymity_nodeHistory (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat)
    (c : PaperHistory.Node G leader r) :
    anonymity G leader r (nodeHistory G leader r c) = PaperHistory.anonymity G leader r c := by
  classical
  unfold anonymity PaperHistory.anonymity PaperHistory.fiber
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← nodeHistory_classOf G leader r a]
  exact (nodeHistory_injective G leader r).eq_iff

/-- All three conclusions of the manuscript lemma, including binary data
size. The level cardinalities are those of actual quotient history nodes. -/
structure PrefixSpec (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (labelBits descriptionBits : Nat) : Prop where
  levels : ∀ r, r ≤ t → Fintype.card (PaperHistory.Node G leader r) ≤
    (∑ j ∈ Finset.range (r + 1), (TimingProtocolLocal.levels t H j).card) + r + 2
  anonymities : ∀ r, r ≤ t → ∀ v ∈ fullLevel G leader r,
    (anonymity G leader r v).size ≤ labelBits
  degrees : ∀ r, r < t → ∀ v ∈ fullLevel G leader (r + 1), (degree r v).size ≤ labelBits
  multiplicities : ∀ r, r < t → ∀ u (v : FullHistory (r + 1)),
    v ∈ fullLevel G leader (r + 1) → (red r u v).size ≤ labelBits
  description : (tableBits G leader t).length ≤ descriptionBits

def labelBitsBound (N M : Nat) := 2 * N.size + M.size + 6

theorem network_spec [DecidableEq A] (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) :
    PrefixSpec (network G leader t H) leader t H
      (labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t H))
      (tableBudget t (2 * Realizability.nodeCount t H + 1)
        (labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t H) +
          (2 * Realizability.nodeCount t H + 1))) := by
  have labels := network_labels G leader t H
  have size := labelCap_size (Fintype.card A) (Realizability.maxLabel 0 t H)
  have anons : ∀ r, r ≤ t → ∀ v ∈ fullLevel (network G leader t H) leader r,
      (anonymity (network G leader t H) leader r v).size ≤
        labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t H) :=
    fun r _ v _ => (Nat.size_le_size (labels.1 r v)).trans size
  have degrees : ∀ r, r < t → ∀ v ∈ fullLevel (network G leader t H) leader (r + 1),
      (degree r v).size ≤ labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t H) :=
    fun r hr v hv => (Nat.size_le_size (labels.2.1 r hr v hv)).trans size
  have reds : ∀ r, r < t → ∀ u (v : FullHistory (r + 1)),
      v ∈ fullLevel (network G leader t H) leader (r + 1) →
      (red r u v).size ≤ labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t H) :=
    fun r hr u v hv => (Nat.size_le_size (labels.2.2 r hr u v hv)).trans size
  refine ⟨?_, anons, degrees, reds, ?_⟩
  · intro r hr
    rw [← fullLevel_card]
    exact network_level_bound G leader t H r hr
  · apply table_bits_bound _ _ _ _ _ (network_level_uniform G leader t H)
    · intro r hr v hv
      exact (anons r hr v hv).trans (Nat.le_add_right _ _)
    · intro r hr v hv
      exact (degrees r hr v hv).trans (Nat.le_add_right _ _)
    · intro r hr u v hv
      exact (reds r hr u v hv).trans (Nat.le_add_right _ _)
    · omega
    · unfold labelBitsBound
      omega

/-- **Small full prefix**, intrinsic form: normalize any realization on
the very same agents with exactly the same leader statuses. -/
theorem small_full_prefix (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (observer : A) {ell : Nat} (valid : Admissible ell G leader) :
    ∃ G' : Nat → A → A → Nat, Admissible ell G' leader ∧
      history G' leader t observer = history G leader t observer ∧
      PrefixSpec G' leader t (history G leader t observer)
        (labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t (history G leader t observer)))
        (tableBudget t (2 * Realizability.nodeCount t (history G leader t observer) + 1)
          (labelBitsBound (Fintype.card A) (Realizability.maxLabel 0 t (history G leader t observer)) +
            (2 * Realizability.nodeCount t (history G leader t observer) + 1))) := by
  classical
  exact ⟨network G leader t _, network_admissible G leader t _ valid,
    network_observer G leader t observer, network_spec G leader t _⟩

theorem tableBudget_polynomial (t nu M N s : Nat)
    (depth : t ≤ s) (nodes : nu ≤ s) (labels : M.size ≤ s + 1) :
    tableBudget t (2 * nu + 1) (labelBitsBound N M + (2 * nu + 1)) ≤
      33 * (s + N.size + 8) ^ 4 := by
  let L := s + N.size + 8
  have pos : 1 ≤ L := by dsimp [L]; omega
  have h₁ : t + 2 ≤ L := by dsimp [L]; omega
  have h₂ : (2 * nu + 1) + 1 ≤ 2 * L := by dsimp [L]; omega
  have h₃ : (2 * nu + 1) + 5 ≤ 2 * L := by dsimp [L]; omega
  have h₄ : 2 * (labelBitsBound N M + (2 * nu + 1)) + 4 ≤ 6 * L := by
    dsimp [labelBitsBound, L]; omega
  have row : ((2 * nu + 1) + 5) * (2 * (labelBitsBound N M + (2 * nu + 1)) + 4) ≤ 12 * L ^ 2 := by
    have := Nat.mul_le_mul h₃ h₄
    nlinarith
  have level : ((2 * nu + 1) + 1) *
      (((2 * nu + 1) + 5) * (2 * (labelBitsBound N M + (2 * nu + 1)) + 4) + 3) ≤ 30 * L ^ 3 := by
    have := Nat.mul_le_mul h₂ (Nat.add_le_add_right row 3)
    have sq : L ≤ L ^ 3 := Nat.le_pow (by omega)
    nlinarith
  unfold tableBudget
  have := Nat.mul_le_mul h₁ (Nat.add_le_add_right level 3)
  have fourth : L ≤ L ^ 4 := Nat.le_pow (by omega)
  change _ ≤ 33 * L ^ 4
  nlinarith

/-- **Small full prefix**, with s the actual binary vista length. This gives
explicit constants for O(s + log N) labels and polynomial total description. -/
theorem encoded_small_full_prefix (v : Executable.Vista) (validVista : v.valid = true)
    (ell N : Nat) (realizable : Realizability.Realizable ell N v.denotes) :
    ∃ (A : Type) (finite : Fintype A),
      letI : Fintype A := finite
      ∃ (G : Nat → A → A → Nat) (leader : A → Bool) (observer : A),
        Fintype.card A = N ∧ Admissible ell G leader ∧
        history G leader (v.node v.bottom).level observer = v.denotes ∧
        PrefixSpec G leader (v.node v.bottom).level v.denotes
          (2 * N.size + (Encoding.vista.encode v).length + 7)
          (33 * ((Encoding.vista.encode v).length + N.size + 8) ^ 4) := by
  classical
  obtain ⟨A, finite, G, leader, observer, order, admissible, hist⟩ := realizable
  letI : Fintype A := finite
  obtain ⟨G', valid, preserves, spec⟩ := small_full_prefix G leader _ observer admissible
  rw [hist, order] at spec
  have labels : (Realizability.maxLabel 0 (v.node v.bottom).level v.denotes).size ≤
      (Encoding.vista.encode v).length + 1 := by
    simpa [Encoding.vistaInput_length] using Encoding.decoded_maxLabel_bits_le v validVista 0
  have nodes : Realizability.nodeCount (v.node v.bottom).level v.denotes ≤
      (Encoding.vista.encode v).length :=
    (Encoding.decoded_nodeCount_le v validVista).trans (Encoding.vista_nodes_le_length v)
  have depth : (v.node v.bottom).level ≤ (Encoding.vista.encode v).length :=
    (RealizabilityVerifier.valid_depth_lt_size v validVista).le.trans
      (Encoding.vista_nodes_le_length v)
  have bits : labelBitsBound N (Realizability.maxLabel 0 (v.node v.bottom).level v.denotes) ≤
      2 * N.size + (Encoding.vista.encode v).length + 7 := by unfold labelBitsBound; omega
  refine ⟨A, finite, G', leader, observer, order, valid, preserves.trans hist, ?_⟩
  exact ⟨spec.levels, fun r hr h hh => (spec.anonymities r hr h hh).trans bits,
    fun r hr h hh => (spec.degrees r hr h hh).trans bits,
    fun r hr u h hh => (spec.multiplicities r hr u h hh).trans bits,
    spec.description.trans (tableBudget_polynomial _ _ _ _ _ depth nodes labels)⟩

end Counting.SmallPrefix
