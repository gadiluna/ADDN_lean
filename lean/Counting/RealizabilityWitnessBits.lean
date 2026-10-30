import Counting.RealizabilitySpectrum
import Counting.SupportBitLength

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

/-- Payload bits of the one natural count per visible node. Framing and
the encoded input representation are deliberately not charged here. -/
noncomputable def countPayloadBits (t : ℕ) (H : FullHistory t) (k : Counts) : ℕ :=
  ∑ r ∈ Finset.range (t + 1), ∑ u ∈ levels t H r, Nat.size (k r u)

variable {ell N t : ℕ} {H : FullHistory t} {k : Counts}

theorem Certificate.count_payload_bound (cert : Certificate ell N t H k) :
    countPayloadBits t H k ≤ nodeCount t H * Nat.size N := by
  calc
    _ ≤ ∑ r ∈ Finset.range (t + 1), (levels t H r).card * Nat.size N := by
      apply Finset.sum_le_sum
      intro r _
      calc
        _ ≤ ∑ _u ∈ levels t H r, Nat.size N :=
          Finset.sum_le_sum (fun u hu => Nat.size_le_size (cert.count_le_order r ⟨u, hu⟩))
        _ = _ := by simp
    _ = _ := by
      unfold nodeCount
      rw [Finset.sum_mul]

theorem bounded_order_bits (ell N t : ℕ) (H : FullHistory t) (L : ℕ)
    (order : N ≤ supportBound ell t H + ell + 2)
    (depth : t ≤ L) (nodes : nodeCount t H ≤ L) (labels : Nat.size (maxLabel ell t H) ≤ L) :
    Nat.size N ≤ 2 * (L + 1) ^ 2 + 1 := by
  apply SupportBitLength.order_size_polynomial N (nodeCount t H) (maxLabel ell t H) t ell L order depth nodes labels
  exact (Nat.size_le_size (Nat.le_max_left ell _)).trans labels

theorem Certificate.bounded_count_payload (cert : Certificate ell N t H k) (L : ℕ)
    (order : N ≤ supportBound ell t H + ell + 2)
    (depth : t ≤ L) (nodes : nodeCount t H ≤ L) (labels : Nat.size (maxLabel ell t H) ≤ L) :
    countPayloadBits t H k ≤ L * (2 * (L + 1) ^ 2 + 1) :=
  cert.count_payload_bound.trans (Nat.mul_le_mul nodes (bounded_order_bits ell N t H L order depth nodes labels))

/-- Distinct compatible orders have count-certificate witnesses whose
order fields and count payloads obey explicit polynomial bounds in any
length L dominating the vista depth, node count and largest label width. -/
theorem polynomial_count_witnesses (ell t : ℕ) (H : FullHistory t) (L : ℕ)
    (depth : t ≤ L) (nodes : nodeCount t H ≤ L) (labels : Nat.size (maxLabel ell t H) ≤ L)
    (multiple : ∃ N₁ N₂, N₁ ≠ N₂ ∧ Realizable ell N₁ H ∧ Realizable ell N₂ H) :
    ∃ N₁ N₂ k₁ k₂, N₁ ≠ N₂ ∧ Certificate ell N₁ t H k₁ ∧ Certificate ell N₂ t H k₂ ∧
      Nat.size N₁ ≤ 2 * (L + 1) ^ 2 + 1 ∧ Nat.size N₂ ≤ 2 * (L + 1) ^ 2 + 1 ∧
      countPayloadBits t H k₁ ≤ L * (2 * (L + 1) ^ 2 + 1) ∧
      countPayloadBits t H k₂ ≤ L * (2 * (L + 1) ^ 2 + 1) := by
  obtain ⟨N₁, N₂, different, firstBound, secondBound, first, second⟩ := bounded_compatible_orders ell H multiple
  obtain ⟨k₁, firstCert⟩ := first.exists_certificate
  obtain ⟨k₂, secondCert⟩ := second.exists_certificate
  exact ⟨N₁, N₂, k₁, k₂, different, firstCert, secondCert,
    bounded_order_bits ell N₁ t H L firstBound depth nodes labels,
    bounded_order_bits ell N₂ t H L secondBound depth nodes labels,
    firstCert.bounded_count_payload L firstBound depth nodes labels,
    secondCert.bounded_count_payload L secondBound depth nodes labels⟩

end Counting.Realizability
