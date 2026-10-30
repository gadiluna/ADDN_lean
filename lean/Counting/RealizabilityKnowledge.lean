import Counting.RealizabilityRecognition
import Counting.DagSemanticsView

namespace Counting.Realizability

/-- Epistemic knowledge: every admissible realization with the same local
history has this order. Realizability quantifies over all finite carriers. -/
def KnowsOrder (ell n : Nat) {t : Nat} (H : FullHistory t) : Prop :=
  ∀ N, Realizable ell N H → N = n

theorem knowsOrder_iff_singleton {ell n t : Nat} {H : FullHistory t}
    (actual : Realizable ell n H) :
    KnowsOrder ell n H ↔ spectrum ell H = {n} := by
  constructor
  · intro known
    ext N
    constructor
    · exact fun realized => Set.mem_singleton_iff.mpr (known N realized)
    · intro member
      have equal := Set.mem_singleton_iff.mp member
      exact equal ▸ actual
  · intro singleton N realized
    have member : N ∈ spectrum ell H := realized
    rw [singleton] at member
    exact Set.mem_singleton_iff.mp member

theorem knowsOrder_iff_atMostOne {ell n t : Nat} {H : FullHistory t}
    (actual : Realizable ell n H) :
    KnowsOrder ell n H ↔ AtMostOneVista ell H := by
  constructor
  · intro known N first M second
    exact (known N first).trans (known M second).symm
  · intro unique N realized
    exact unique realized actual

/-- The encoding convention: malformed DAGs have empty spectrum. A valid
DAG is interpreted by its decoded pointed labeled vista. This is a semantic
definition; machine costs of validation are proved separately. -/
noncomputable def encodedSpectrum (ell : Nat) (vista : Executable.Vista) : Set Nat :=
  if vista.valid then spectrum ell vista.denotes else ∅

theorem encodedSpectrum_invalid (ell : Nat) (vista : Executable.Vista)
    (invalid : vista.valid = false) : encodedSpectrum ell vista = ∅ := by
  simp [encodedSpectrum, invalid]

theorem encodedSpectrum_valid (ell : Nat) (vista : Executable.Vista)
    (valid : vista.valid = true) : encodedSpectrum ell vista = spectrum ell vista.denotes := by
  simp [encodedSpectrum, valid]

theorem encodedSpectrum_unique_iff_knows (ell n : Nat) (vista : Executable.Vista)
    (valid : vista.valid = true) (actual : Realizable ell n vista.denotes) :
    (encodedSpectrum ell vista).Subsingleton ↔ KnowsOrder ell n vista.denotes := by
  rw [encodedSpectrum_valid ell vista valid]
  exact (knowsOrder_iff_atMostOne actual).symm

end Counting.Realizability
