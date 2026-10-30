import Counting.RealizabilityWitnessBits

/-! Semantic recognition problems and their compact mathematical witnesses.
These predicates concern intrinsic vistas and the distributed network
model. Encoded syntax, decision procedures and machine cost are separate.
-/

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

def AtMostOneVista (ell : ℕ) {t : ℕ} (H : FullHistory t) : Prop :=
  (spectrum ell H).Subsingleton

theorem not_atMostOne_iff_two (ell : ℕ) {t : ℕ} (H : FullHistory t) :
    ¬ AtMostOneVista ell H ↔
      ∃ N₁ N₂, N₁ ≠ N₂ ∧ Realizable ell N₁ H ∧ Realizable ell N₂ H := by
  classical
  constructor
  · intro notUnique
    by_contra noTwo
    apply notUnique
    intro N₁ first N₂ second
    by_contra different
    exact noTwo ⟨N₁, N₂, different, first, second⟩
  · rintro ⟨N₁, N₂, different, first, second⟩ unique
    exact different (unique first second)

/-- The complement has two bounded compatible-order count certificates. -/
theorem not_atMostOne_iff_certificates (ell : ℕ) {t : ℕ} (H : FullHistory t) :
    ¬ AtMostOneVista ell H ↔
      ∃ N₁ N₂ k₁ k₂, N₁ ≠ N₂ ∧ N₁ ≤ supportBound ell t H + ell + 2 ∧
        N₂ ≤ supportBound ell t H + ell + 2 ∧ Certificate ell N₁ t H k₁ ∧ Certificate ell N₂ t H k₂ := by
  constructor
  · intro no
    obtain ⟨N₁, N₂, different, firstBound, secondBound, first, second⟩ :=
      bounded_compatible_orders ell H ((not_atMostOne_iff_two ell H).mp no)
    obtain ⟨k₁, firstCert⟩ := first.exists_certificate
    obtain ⟨k₂, secondCert⟩ := second.exists_certificate
    exact ⟨N₁, N₂, k₁, k₂, different, firstBound, secondBound, firstCert, secondCert⟩
  · rintro ⟨N₁, N₂, k₁, k₂, different, _, _, firstCert, secondCert⟩
    exact (not_atMostOne_iff_two ell H).mpr ⟨N₁, N₂, different, firstCert.realizable, secondCert.realizable⟩

theorem not_atMostOne_iff_alternate {ell n t : ℕ} {H : FullHistory t}
    (actual : Realizable ell n H) :
    ¬ AtMostOneVista ell H ↔
      ∃ N k, N ≠ n ∧ N ≤ supportBound ell t H + ell + 2 ∧ Certificate ell N t H k := by
  classical
  constructor
  · intro no
    obtain ⟨N₁, N₂, k₁, k₂, different, firstBound, secondBound, firstCert, secondCert⟩ :=
      (not_atMostOne_iff_certificates ell H).mp no
    by_cases first : N₁ = n
    · exact ⟨N₂, k₂, by intro eq; exact different (first.trans eq.symm), secondBound, secondCert⟩
    · exact ⟨N₁, k₁, first, firstBound, firstCert⟩
  · rintro ⟨N, k, different, _, cert⟩ unique
    exact different (unique cert.realizable actual)

variable {V : Type} [Fintype V]
variable (ell : ℕ) (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ)

/-- Admissibility is part of the semantic network problem, so an invalid
network has a negative answer, as stipulated for the eventual encoding. -/
def SomeAgentKnows : Prop :=
  Admissible ell G leader ∧ ∃ a, AtMostOneVista ell (history G leader t a)

theorem someAgentKnows_false_of_invalid (invalid : ¬ Admissible ell G leader) :
    ¬ SomeAgentKnows ell G leader t := fun knows => invalid knows.1

theorem actual_history_realizable (valid : Admissible ell G leader) (a : V) :
    Realizable ell (Fintype.card V) (history G leader t a) :=
  ⟨V, inferInstance, G, leader, a, rfl, valid, rfl⟩

theorem not_someAgentKnows_iff_each (valid : Admissible ell G leader) :
    ¬ SomeAgentKnows ell G leader t ↔ ∀ a, ¬ AtMostOneVista ell (history G leader t a) := by
  constructor
  · intro no a unique
    exact no ⟨valid, a, unique⟩
  · rintro every ⟨_, a, unique⟩
    exact every a unique

/-- On valid networks, the complement has one alternate-order certificate
for each listed agent, with an order bounded by that agent's vista. -/
theorem not_someAgentKnows_iff_certificates (valid : Admissible ell G leader) :
    ¬ SomeAgentKnows ell G leader t ↔
      ∃ orders : V → ℕ, ∃ counts : V → Counts, ∀ a,
        orders a ≠ Fintype.card V ∧
        orders a ≤ supportBound ell t (history G leader t a) + ell + 2 ∧
        Certificate ell (orders a) t (history G leader t a) (counts a) := by
  classical
  rw [not_someAgentKnows_iff_each ell G leader t valid]
  constructor
  · intro every
    have witnesses : ∀ a, ∃ N k, N ≠ Fintype.card V ∧
        N ≤ supportBound ell t (history G leader t a) + ell + 2 ∧
        Certificate ell N t (history G leader t a) k := fun a =>
      (not_atMostOne_iff_alternate (actual_history_realizable ell G leader t valid a)).mp (every a)
    choose orders counts proof using witnesses
    exact ⟨orders, counts, proof⟩
  · rintro ⟨orders, counts, proof⟩ a
    exact (not_atMostOne_iff_alternate (actual_history_realizable ell G leader t valid a)).mpr
      ⟨orders a, counts a, proof a⟩

/-- Both agreed invalid-input branches are explicit: an inadmissible
network belongs to the complement without requiring agent witnesses. -/
theorem not_someAgentKnows_iff_invalid_or_certificates :
    ¬ SomeAgentKnows ell G leader t ↔
      ¬ Admissible ell G leader ∨
        ∃ orders : V → ℕ, ∃ counts : V → Counts, ∀ a,
          orders a ≠ Fintype.card V ∧
          orders a ≤ supportBound ell t (history G leader t a) + ell + 2 ∧
          Certificate ell (orders a) t (history G leader t a) (counts a) := by
  classical
  by_cases valid : Admissible ell G leader
  · simpa only [valid, not_true_eq_false, false_or] using
      not_someAgentKnows_iff_certificates ell G leader t valid
  · simp only [valid, not_false_eq_true, true_or, iff_true]
    exact someAgentKnows_false_of_invalid ell G leader t valid

end Counting.Realizability
