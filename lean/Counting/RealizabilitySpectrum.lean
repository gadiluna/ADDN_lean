import Counting.RealizabilitySupport
import Counting.RealizabilityComplete

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

/-- Compatible orders for the intrinsic vista, with the known leader
count fixed across every admissible realizing population. -/
def spectrum (ell : ℕ) {t : ℕ} (H : FullHistory t) : Set ℕ :=
  {N | Realizable ell N H}

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) {ell : ℕ}

/-- The paper's pumping assertion applies to the actual proper causal
support of the observer and yields admissible realizations at every larger
order, with exactly ell leaders. -/
theorem pumping_of_open_realization (valid : Admissible ell G leader) (t : ℕ) (observer : V)
    (proper : causalSupport G 0 t observer ≠ Finset.univ) (N' : ℕ) (larger : Fintype.card V ≤ N') :
    Realizable ell N' (history G leader t observer) := by
  have cert := pumped_certificate_of_actual G leader valid t observer proper (N' - Fintype.card V)
  rw [Nat.add_sub_of_le larger] at cert
  exact cert.realizable

theorem eventual_of_open_realization (valid : Admissible ell G leader) (t : ℕ) (observer : V)
    (proper : causalSupport G 0 t observer ≠ Finset.univ) :
    ∃ threshold ≤ supportBound ell t (history G leader t observer) + ell + 1,
      ∀ N', threshold ≤ N' → Realizable ell N' (history G leader t observer) := by
  let cert := certificate_of_actual G leader valid t observer
  let threshold := ell + initialCount (levels t (history G leader t observer))
    (selectedCounts G leader t observer) false + 1
  refine ⟨threshold, cert.eventual_threshold_le _ (selected_initial_le_bound G leader t observer ell), ?_⟩
  intro N' larger
  have next := cert.eventual (actual_counts_open G leader t observer proper) (N' - threshold)
  change Certificate ell (threshold + (N' - threshold)) t (history G leader t observer)
    (selectedCounts G leader t observer) at next
  rw [Nat.add_sub_of_le larger] at next
  exact next.realizable

variable {N t : ℕ} {H : FullHistory t}

/-- Any order exceeding the vista's intrinsic support bound necessarily
has proper initial causal support, so the constructive pumping theorem
gives an eventual interval with the paper's threshold. -/
theorem Realizable.eventual_of_large (realizable : Realizable ell N H)
    (large : supportBound ell t H < N) :
    ∃ threshold ≤ supportBound ell t H + ell + 1,
      ∀ N', threshold ≤ N' → Realizable ell N' H := by
  obtain ⟨A, finite, G, leader, observer, order, valid, hist⟩ := realizable
  letI : Fintype A := finite
  have proper : causalSupport G 0 t observer ≠ Finset.univ := by
    intro closed
    have bound := initial_support_le_bound G leader t observer ell
    rw [closed, Finset.card_univ, order, hist] at bound
    omega
  simpa only [hist] using eventual_of_open_realization G leader valid t observer proper

theorem bounded_or_eventual (ell : ℕ) {t : ℕ} (H : FullHistory t) :
    (∀ N, Realizable ell N H → N ≤ supportBound ell t H) ∨
      ∃ threshold ≤ supportBound ell t H + ell + 1,
        ∀ N, threshold ≤ N → Realizable ell N H := by
  classical
  by_cases bounded : ∀ N, Realizable ell N H → N ≤ supportBound ell t H
  · exact Or.inl bounded
  · push Not at bounded
    obtain ⟨N, realizes, large⟩ := bounded
    exact Or.inr (realizes.eventual_of_large large)

/-- The exact mathematical bound K+ell+2 for two distinct compatible
orders. Polynomial bit length of K is a separate encoding/cost theorem. -/
theorem bounded_compatible_orders (ell : ℕ) {t : ℕ} (H : FullHistory t)
    (multiple : ∃ N₁ N₂, N₁ ≠ N₂ ∧ Realizable ell N₁ H ∧ Realizable ell N₂ H) :
    ∃ N₁ N₂, N₁ ≠ N₂ ∧ N₁ ≤ supportBound ell t H + ell + 2 ∧
      N₂ ≤ supportBound ell t H + ell + 2 ∧ Realizable ell N₁ H ∧ Realizable ell N₂ H := by
  rcases bounded_or_eventual ell H with bounded | ⟨threshold, small, eventual⟩
  · obtain ⟨N₁, N₂, different, first, second⟩ := multiple
    exact ⟨N₁, N₂, different, by have := bounded N₁ first; omega,
      by have := bounded N₂ second; omega, first, second⟩
  · refine ⟨supportBound ell t H + ell + 1, supportBound ell t H + ell + 2,
      by omega, by omega, by omega, eventual _ small, eventual _ (by omega)⟩

theorem spectrum_finite_or_cofinite (ell : ℕ) {t : ℕ} (H : FullHistory t) :
    (spectrum ell H).Finite ∨ (spectrum ell H)ᶜ.Finite := by
  rcases bounded_or_eventual ell H with bounded | ⟨threshold, _, eventual⟩
  · exact Or.inl ((Set.finite_Iic _).subset (fun _ h => bounded _ h))
  · apply Or.inr
    apply (Set.finite_Iio threshold).subset
    intro N outside
    by_contra hn
    exact outside (eventual N (by exact Nat.le_of_not_gt hn))

end Counting.Realizability
