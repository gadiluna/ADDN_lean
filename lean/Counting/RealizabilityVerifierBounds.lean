import Counting.RealizabilityVerifierComplete
import Mathlib.Data.Nat.Size

namespace Counting.RealizabilityVerifier
open Counting.Executable Counting.TimingProtocolLocal
open scoped BigOperators

/-- Numeric payload only; the surrounding encoding is charged separately. -/
def payloadBits (weights : Array ℕ) : ℕ :=
  ∑ i : Fin weights.size, Nat.size (weight weights i.val)

theorem valid_level_le_index (vista : Vista) (valid : vista.valid = true) (i : ℕ)
    (inside : i < vista.nodes.size) : (vista.node i).level ≤ i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases zero : (vista.node i).level = 0
      · omega
      · obtain ⟨p, _, before, level, _, _, _⟩ :=
          nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) zero
        have prior := ih p before (before.trans inside)
        omega

/-- A valid DAG's round loop is bounded by its stored representation. -/
theorem valid_depth_lt_size (vista : Vista) (valid : vista.valid = true) :
    (vista.node vista.bottom).level < vista.nodes.size :=
  (valid_level_le_index vista valid vista.bottom (bottom_inside vista valid)).trans_lt
    (bottom_inside vista valid)

theorem accepted_weight_le_order (vista : Vista) (weights : Array ℕ) (ell N : ℕ)
    (accepted : verify vista weights ell N = true) (i : ℕ) (inside : i < vista.nodes.size) :
    weight weights i ≤ N := by
  obtain ⟨valid, _, cert⟩ := (verify_iff_certificate vista weights ell N).mp accepted
  have bound := cert.count_le_order (vista.node i).level
    ⟨decodeNode vista (vista.node i).level i, stored_history_visible vista valid i inside⟩
  rw [decodedWeight_decode vista valid weights _ i
    ((mem_levelNodes _ _ _).mpr ⟨inside, rfl⟩)] at bound
  exact bound

theorem accepted_payload_bound (vista : Vista) (weights : Array ℕ) (ell N : ℕ)
    (accepted : verify vista weights ell N = true) :
    payloadBits weights ≤ vista.nodes.size * Nat.size N := by
  have length := ((verify_iff_certificate vista weights ell N).mp accepted).2.1
  calc
    _ ≤ ∑ _i : Fin weights.size, Nat.size N := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.size_le_size (accepted_weight_le_order vista weights ell N accepted i.val (by
        simpa only [length] using i.isLt))
    _ = _ := by simp [length]

theorem exists_bounded_verified (vista : Vista) (valid : vista.valid = true) (ell N : ℕ)
    (realization : Realizability.Realizable ell N vista.denotes) :
    ∃ weights, verify vista weights ell N = true ∧
      payloadBits weights ≤ vista.nodes.size * Nat.size N := by
  obtain ⟨weights, accepted⟩ := (exists_verified_iff vista ell N).mpr ⟨valid, realization⟩
  exact ⟨weights, accepted, accepted_payload_bound vista weights ell N accepted⟩

/-- The verifier graph size depends only on stored node indices, even if
the certificate claims a population with exponentially many agents. -/
theorem roundVertex_card_bound (N : ℕ) (vista : Vista) (weights : Array ℕ) (r : ℕ) :
    Fintype.card (RoundVertex N vista weights r) ≤ 2 * vista.nodes.size + 1 := by
  have oldBound : Fintype.card (LevelIndex vista r) ≤ vista.nodes.size := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun i : Fin vista.nodes.size => (vista.node i.val).level = r)
  have newBound : Fintype.card (LevelIndex vista (r + 1)) ≤ vista.nodes.size := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun i : Fin vista.nodes.size => (vista.node i.val).level = r + 1)
  have outsideBound : outsideSize N vista weights r ≤ 1 := by
    unfold outsideSize
    split_ifs <;> omega
  change Fintype.card (LevelIndex vista (r + 1) ⊕
    (LevelIndex vista r ⊕ Fin (outsideSize N vista weights r))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end Counting.RealizabilityVerifier
