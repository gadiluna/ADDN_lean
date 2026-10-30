import Counting.RealizabilityRecognition

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

theorem vista_complement_polynomial_witnesses (ell t : ℕ) (H : FullHistory t) (L : ℕ)
    (depth : t ≤ L) (nodes : nodeCount t H ≤ L) (labels : Nat.size (maxLabel ell t H) ≤ L)
    (no : ¬ AtMostOneVista ell H) :
    ∃ N₁ N₂ k₁ k₂, N₁ ≠ N₂ ∧ Certificate ell N₁ t H k₁ ∧ Certificate ell N₂ t H k₂ ∧
      Nat.size N₁ ≤ 2 * (L + 1) ^ 2 + 1 ∧ Nat.size N₂ ≤ 2 * (L + 1) ^ 2 + 1 ∧
      countPayloadBits t H k₁ ≤ L * (2 * (L + 1) ^ 2 + 1) ∧
      countPayloadBits t H k₂ ≤ L * (2 * (L + 1) ^ 2 + 1) :=
  polynomial_count_witnesses ell t H L depth nodes labels ((not_atMostOne_iff_two ell H).mp no)

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ)

/-- Order fields and count payloads for one alternate certificate per
agent. This excludes framing and is not a runtime bound. -/
noncomputable def networkWitnessPayload (orders : V → ℕ) (counts : V → Counts) : ℕ :=
  ∑ a : V, (Nat.size (orders a) + countPayloadBits t (history G leader t a) (counts a))

theorem network_complement_polynomial_witnesses (ell : ℕ) (valid : Admissible ell G leader)
    (no : ¬ SomeAgentKnows ell G leader t) (L : ℕ)
    (depth : t ≤ L)
    (nodes : ∀ a, nodeCount t (history G leader t a) ≤ L)
    (labels : ∀ a, Nat.size (maxLabel ell t (history G leader t a)) ≤ L) :
    ∃ orders : V → ℕ, ∃ counts : V → Counts,
      (∀ a, orders a ≠ Fintype.card V ∧
        Certificate ell (orders a) t (history G leader t a) (counts a)) ∧
      (∀ a, Nat.size (orders a) ≤ 2 * (L + 1) ^ 2 + 1) ∧
      (∀ a, countPayloadBits t (history G leader t a) (counts a) ≤ L * (2 * (L + 1) ^ 2 + 1)) ∧
      networkWitnessPayload G leader t orders counts ≤
        Fintype.card V * ((L + 1) * (2 * (L + 1) ^ 2 + 1)) := by
  obtain ⟨orders, counts, proof⟩ := (not_someAgentKnows_iff_certificates ell G leader t valid).mp no
  have orderBits (a : V) : Nat.size (orders a) ≤ 2 * (L + 1) ^ 2 + 1 :=
    bounded_order_bits ell (orders a) t (history G leader t a) L (proof a).2.1 depth (nodes a) (labels a)
  have countBits (a : V) : countPayloadBits t (history G leader t a) (counts a) ≤ L * (2 * (L + 1) ^ 2 + 1) :=
    (proof a).2.2.bounded_count_payload L (proof a).2.1 depth (nodes a) (labels a)
  refine ⟨orders, counts, fun a => ⟨(proof a).1, (proof a).2.2⟩, orderBits, countBits, ?_⟩
  calc
    _ ≤ ∑ _a : V, (L + 1) * (2 * (L + 1) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro a _
      have := Nat.add_le_add (orderBits a) (countBits a)
      nlinarith
    _ = _ := by simp

/-- If the explicit network length also bounds its listed agent count,
the total numerical witness payload is polynomial in the same L. -/
theorem network_complement_payload_polynomial (ell : ℕ) (valid : Admissible ell G leader)
    (no : ¬ SomeAgentKnows ell G leader t) (L : ℕ)
    (agents : Fintype.card V ≤ L) (depth : t ≤ L)
    (nodes : ∀ a, nodeCount t (history G leader t a) ≤ L)
    (labels : ∀ a, Nat.size (maxLabel ell t (history G leader t a)) ≤ L) :
    ∃ orders : V → ℕ, ∃ counts : V → Counts,
      (∀ a, orders a ≠ Fintype.card V ∧
        Certificate ell (orders a) t (history G leader t a) (counts a)) ∧
      networkWitnessPayload G leader t orders counts ≤
        L * ((L + 1) * (2 * (L + 1) ^ 2 + 1)) := by
  obtain ⟨orders, counts, correct, _, _, payload⟩ :=
    network_complement_polynomial_witnesses G leader t ell valid no L depth nodes labels
  exact ⟨orders, counts, correct, payload.trans (Nat.mul_le_mul_right _ agents)⟩

end Counting.Realizability
