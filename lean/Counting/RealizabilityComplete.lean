import Counting.RealizabilitySufficiency
import Counting.RealizabilitySingleton
import Counting.RealizabilityNecessity

/-! Fixed-order realizability of intrinsic vistas. This equivalence concerns
the mathematical certificate. StackRealizabilityMachine supplies the compact
encoded verifier and its polynomial physical running-time bound. -/

namespace Counting.Realizability

/-- Realization by an admissible finite population of exactly the requested
order. Histories specify the vista up to the proved pointed isomorphism. -/
def Realizable (ell N : Nat) {t : Nat} (H : FullHistory t) : Prop :=
  ∃ (A : Type) (finite : Fintype A),
    letI : Fintype A := finite
    ∃ (G : Nat → A → A → Nat) (leader : A → Bool) (observer : A),
      Fintype.card A = N ∧ Admissible ell G leader ∧ history G leader t observer = H

variable {ell N t : Nat} {H : FullHistory t} {k : Counts}

theorem Certificate.realizable (cert : Certificate ell N t H k) : Realizable ell N H := by
  by_cases singleton : N = 1
  · subst N
    obtain ⟨G, valid, hist⟩ := cert.singleton_realization
    exact ⟨Unit, inferInstance, G, (fun _ => true), (), by simp, valid, hist⟩
  · have many : 1 < N := by have := cert.leaders_positive; have := cert.order_ge_leaders; omega
    obtain ⟨G, valid, a, hist⟩ := cert.realization_of_many many
    exact ⟨CountAllocation.Population N ell, inferInstance, G,
      CountAllocation.populationLeader N ell, a,
      CountAllocation.population_card N ell cert.order_ge_leaders, valid, hist⟩

theorem Realizable.exists_certificate (realizable : Realizable ell N H) :
    ∃ k, Certificate ell N t H k := by
  obtain ⟨A, finite, G, leader, observer, order, valid, hist⟩ := realizable
  letI : Fintype A := finite
  obtain ⟨k, cert⟩ := exists_certificate_of_actual G leader valid t observer
  exact ⟨k, order ▸ hist ▸ cert⟩

/-- Full mathematical equivalence, including order one, depth zero, loops,
parallel arcs, and exact leader count. No bound on physical graph size is
claimed by this existential construction. -/
theorem fixed_order_iff_certificate : Realizable ell N H ↔ ∃ k, Certificate ell N t H k :=
  ⟨Realizable.exists_certificate, fun ⟨_, cert⟩ => cert.realizable⟩

end Counting.Realizability
