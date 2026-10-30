import Counting.RealizabilityConnected

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- The actual causal support supplies all fields of the paper's compact
fixed-order realizability certificate, including the auxiliary strong
connectivity test. These are selected counts, not full fiber sizes. -/
theorem certificate_of_actual {ell : ℕ} (valid : Admissible ell G leader)
    (t : ℕ) (observer : V) :
    Certificate ell (Fintype.card V) t (history G leader t observer)
      (selectedCounts G leader t observer) where
  leaders_positive := valid.positive
  order_ge_leaders := valid.leaderCount_le_card
  positive := fun r hr H visible => (selectedCounts_positive_iff G leader t observer r hr H).mpr visible
  bottom_one := selectedCounts_bottom G leader t observer
  initial_leaders := by
    have bound := initialCount_bound G leader t observer true
    exact bound.trans_eq valid.leaders
  initial_nonleaders := by
    have bound := initialCount_bound G leader t observer false
    have sum := nonleader_card_add_leader_card leader
    rw [valid.leaders] at sum
    omega
  parent_visible := fun r hr H hv => actual_parent_visible G leader t observer r hr H hv
  refinement := fun r hr H _ => selectedCounts_refinement G leader t observer r hr H
  balance_full := fun r hr hz H _ => selected_balance_full G leader t observer r hr hz H
  balance_no_leaving := fun r hr _ H _ hz => selected_balance_no_leaving G leader t observer r hr H hz
  connected := fun r hr many => selected_connected G leader t observer r hr (valid.connected (r + 1) (by omega)) many

theorem exists_certificate_of_actual {ell : ℕ} (valid : Admissible ell G leader)
    (t : ℕ) (observer : V) :
    ∃ k, Certificate ell (Fintype.card V) t (history G leader t observer) k :=
  ⟨selectedCounts G leader t observer, certificate_of_actual G leader valid t observer⟩

end Counting.Realizability
