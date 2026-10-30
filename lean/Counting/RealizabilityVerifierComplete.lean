import Counting.RealizabilityVerifierCorrectness
import Counting.RealizabilityVerifierCounts
import Counting.RealizabilityComplete

namespace Counting.RealizabilityVerifier
open Counting.Executable Counting.TimingProtocolLocal

/-- Proof-only serialization of a mathematical certificate. The verifier
itself receives this array and does not call this history decoder. -/
noncomputable def encodeCounts (vista : Vista) (k : Realizability.Counts) : Array ℕ :=
  Array.ofFn (fun i : Fin vista.nodes.size =>
    k (vista.node i.val).level (decodeNode vista (vista.node i.val).level i.val))

@[simp] theorem encodeCounts_size (vista : Vista) (k : Realizability.Counts) :
    (encodeCounts vista k).size = vista.nodes.size := Array.size_ofFn

theorem encodeCounts_get (vista : Vista) (k : Realizability.Counts) (r i : ℕ)
    (inside : i < vista.nodes.size) (level : (vista.node i).level = r) :
    weight (encodeCounts vista k) i = k r (decodeNode vista r i) := by
  unfold weight encodeCounts
  rw [Array.getElem?_ofFn, dif_pos inside, Option.getD_some]
  subst r
  rfl

theorem encodeCounts_agree (vista : Vista) (valid : vista.valid = true) (k : Realizability.Counts) :
    Realizability.CountsAgree (levels (vista.node vista.bottom).level vista.denotes)
      k (decodedWeight vista (encodeCounts vista k)) := by
  intro r H visible
  rw [← decodedLevel_eq_levels vista valid] at visible
  obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel _ _ _).mp visible
  rw [decodedWeight_decode vista valid (encodeCounts vista k) r i
    ((mem_levelNodes _ _ _).mpr ⟨inside, level⟩)]
  exact (encodeCounts_get vista k r i inside level).symm

theorem verify_encodeCounts (vista : Vista) (valid : vista.valid = true) (ell N : ℕ)
    (k : Realizability.Counts)
    (cert : Realizability.Certificate ell N (vista.node vista.bottom).level vista.denotes k) :
    verify vista (encodeCounts vista k) ell N = true := by
  apply (verify_iff_certificate _ _ _ _).mpr
  exact ⟨valid, encodeCounts_size vista k, cert.congr_counts (encodeCounts_agree vista valid k)⟩

theorem verify_sound (vista : Vista) (weights : Array ℕ) (ell N : ℕ)
    (accepted : verify vista weights ell N = true) : Realizability.Realizable ell N vista.denotes :=
  ((verify_iff_certificate vista weights ell N).mp accepted).2.2.realizable

/-- The compact executable verifier accepts some array exactly for valid
DAGs whose denoted vista is realizable at the requested order. This is a
functional correctness theorem; a Turing-machine cost bound is separate. -/
theorem exists_verified_iff (vista : Vista) (ell N : ℕ) :
    (∃ weights, verify vista weights ell N = true) ↔
      vista.valid = true ∧ Realizability.Realizable ell N vista.denotes := by
  constructor
  · rintro ⟨weights, accepted⟩
    exact ⟨((verify_iff_certificate vista weights ell N).mp accepted).1,
      verify_sound vista weights ell N accepted⟩
  · rintro ⟨valid, realization⟩
    obtain ⟨k, cert⟩ := realization.exists_certificate
    exact ⟨encodeCounts vista k, verify_encodeCounts vista valid ell N k cert⟩

end Counting.RealizabilityVerifier
