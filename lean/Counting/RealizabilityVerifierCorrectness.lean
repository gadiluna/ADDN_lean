import Counting.RealizabilityVerifierTransport

namespace Counting.RealizabilityVerifier
open Counting.Executable Counting.TimingProtocolLocal

theorem Checks.certificate {vista : Vista} {weights : Array ℕ} {ell N : ℕ}
    (checks : Checks vista weights ell N) :
    Realizability.Certificate ell N (vista.node vista.bottom).level vista.denotes
      (decodedWeight vista weights) := by
  have valid := checks.valid
  refine ⟨checks.leaders_positive, checks.order_ge_leaders, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _ H visible
    rw [← decodedLevel_eq_levels vista valid] at visible
    obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
    rw [decodedWeight_decode vista valid weights r i ((mem_levelNodes _ _ _).mpr ⟨inside, level⟩)]
    exact checks.positive ⟨i, inside⟩
  · change decodedWeight vista weights (vista.node vista.bottom).level
      (decodeNode vista (vista.node vista.bottom).level vista.bottom) = 1
    rw [decodedWeight_decode vista valid weights _ _
      ((mem_levelNodes _ _ _).mpr ⟨bottom_inside vista valid, rfl⟩)]
    exact checks.bottom_one
  · rw [initialCount_decode vista valid weights true]
    exact checks.initial_leaders
  · rw [initialCount_decode vista valid weights false]
    exact checks.initial_nonleaders
  · intro r _ H visible
    rw [← decodedLevel_eq_levels vista valid] at visible ⊢
    exact decoded_parent_visible vista valid r H visible
  · intro r hr H visible
    rw [← decodedLevel_eq_levels vista valid] at visible
    obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
    let u : LevelIndex vista r := ⟨⟨i, inside⟩, level⟩
    rw [childCount_decode vista valid weights r u,
      decodedWeight_decode vista valid weights r i (levelIndex_present vista r u)]
    exact checks.refinement r hr u
  · intro r hr full H visible
    rw [hidden_decode N vista valid weights r] at full
    rw [← decodedLevel_eq_levels vista valid] at visible
    obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
    let u : LevelIndex vista r := ⟨⟨i, inside⟩, level⟩
    rw [supply_decode vista valid weights r u, demand_decode vista valid weights r u]
    exact checks.balance_full r hr full u
  · intro r hr proper H visible noLeaving
    rw [hidden_decode N vista valid weights r] at proper
    rw [← decodedLevel_eq_levels vista valid] at visible
    obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
    let u : LevelIndex vista r := ⟨⟨i, inside⟩, level⟩
    rw [leaving_decode vista valid weights r u] at noLeaving
    rw [supply_decode vista valid weights r u, demand_decode vista valid weights r u]
    exact checks.balance_no_leaving r hr proper u noLeaving
  · intro r hr many
    exact (connected_decode N vista valid weights r).mp (checks.connected r hr many)

theorem checks_of_certificate (vista : Vista) (valid : vista.valid = true)
    (weights : Array ℕ) (length : weights.size = vista.nodes.size) (ell N : ℕ)
    (cert : Realizability.Certificate ell N (vista.node vista.bottom).level vista.denotes
      (decodedWeight vista weights)) : Checks vista weights ell N := by
  refine ⟨valid, length, cert.leaders_positive, cert.order_ge_leaders, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have positive := cert.positive (vista.node i.val).level (stored_level_le vista valid i)
      _ (stored_history_visible vista valid i.val i.isLt)
    rw [decodedWeight_decode vista valid weights _ i.val
      ((mem_levelNodes _ _ _).mpr ⟨i.isLt, rfl⟩)] at positive
    exact positive
  · have bottom := cert.bottom_one
    change decodedWeight vista weights (vista.node vista.bottom).level
      (decodeNode vista (vista.node vista.bottom).level vista.bottom) = 1 at bottom
    rw [decodedWeight_decode vista valid weights _ vista.bottom
      ((mem_levelNodes _ _ _).mpr ⟨bottom_inside vista valid, rfl⟩)] at bottom
    exact bottom
  · simpa only [initialCount_decode vista valid weights true] using cert.initial_leaders
  · simpa only [initialCount_decode vista valid weights false] using cert.initial_nonleaders
  · intro r hr u
    have h := cert.refinement r hr _ (levelDecode vista valid r u).property
    simpa only [weight, levelDecode, childCount_decode vista valid weights r u,
      decodedWeight_decode vista valid weights r u.val.val (levelIndex_present vista r u)] using h
  · intro r hr full u
    have full' : Realizability.hidden N (levels (vista.node vista.bottom).level vista.denotes)
        (decodedWeight vista weights) r = 0 := by rw [hidden_decode N vista valid weights r, full]
    have h := cert.balance_full r hr full' _ (levelDecode vista valid r u).property
    simpa only [levelDecode, supply_decode vista valid weights r u,
      demand_decode vista valid weights r u] using h
  · intro r hr proper u noLeaving
    have proper' : 0 < Realizability.hidden N (levels (vista.node vista.bottom).level vista.denotes)
        (decodedWeight vista weights) r := by rw [hidden_decode N vista valid weights r]; exact proper
    have noLeaving' : Realizability.leaving (levels (vista.node vista.bottom).level vista.denotes)
        (decodedWeight vista weights) r (decodeNode vista r u.val.val) = 0 := by
      rw [leaving_decode vista valid weights r u, noLeaving]
    have h := cert.balance_no_leaving r hr proper' _ (levelDecode vista valid r u).property noLeaving'
    simpa only [levelDecode, supply_decode vista valid weights r u, demand_decode vista valid weights r u] using h
  · intro r hr many
    exact (connected_decode N vista valid weights r).mpr (cert.connected r hr many)

/-- Exact correspondence for the complete executable fixed-order verifier,
including rejection of malformed DAGs and incorrectly sized count arrays. -/
theorem verify_iff_certificate (vista : Vista) (weights : Array ℕ) (ell N : ℕ) :
    verify vista weights ell N = true ↔ vista.valid = true ∧ weights.size = vista.nodes.size ∧
      Realizability.Certificate ell N (vista.node vista.bottom).level vista.denotes
        (decodedWeight vista weights) := by
  rw [verify_iff_checks]
  exact ⟨fun checks => ⟨checks.valid, checks.length, checks.certificate⟩,
    fun ⟨valid, length, cert⟩ => checks_of_certificate vista valid weights length ell N cert⟩

end Counting.RealizabilityVerifier
