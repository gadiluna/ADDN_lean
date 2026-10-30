import Counting.RealizabilityVerifierTransport

namespace Counting.Realizability
open Counting.TimingProtocolLocal Counting.Executable

def CountsAgree (visible : Levels) (k l : Counts) : Prop :=
  ∀ r H, H ∈ visible r → k r H = l r H

theorem childCount_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (r : ℕ) (u : Counting.FullHistory r) : childCount visible k r u = childCount visible l r u := by
  apply Finset.sum_congr rfl
  intro v hv
  exact agree (r + 1) v (Finset.mem_filter.mp hv).1

theorem supply_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (r : ℕ) (u : Counting.FullHistory r) : supply visible k r u = supply visible l r u := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [agree (r + 1) v (Finset.mem_filter.mp hv).1]

theorem demand_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (r : ℕ) (u : Counting.FullHistory r) : demand visible k r u = demand visible l r u := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [agree (r + 1) v hv]

theorem hidden_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (N r : ℕ) : hidden N visible k r = hidden N visible l r := by
  unfold hidden
  congr 1
  exact Finset.sum_congr rfl (fun v hv => agree (r + 1) v hv)

theorem leaving_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (r : ℕ) (u : Counting.FullHistory r) (visibleU : u ∈ visible r) :
    leaving visible k r u = leaving visible l r u := by
  unfold leaving
  rw [agree r u visibleU, childCount_congr agree]

theorem initialCount_congr {visible : Levels} {k l : Counts} (agree : CountsAgree visible k l)
    (b : Bool) : initialCount visible k b = initialCount visible l b := by
  unfold initialCount
  split_ifs with present
  · exact agree 0 b present
  · rfl

noncomputable def roundCountsEquiv {visible : Levels} {k l : Counts}
    (agree : CountsAgree visible k l) (N r : ℕ) :
    RoundVertex N visible k r ≃ RoundVertex N visible l r :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (finCongr (by
    unfold outsideSize
    rw [hidden_congr agree])))

theorem roundArc_counts_iff {visible : Levels} {k l : Counts}
    (agree : CountsAgree visible k l) (N r : ℕ) (x y : RoundVertex N visible k r) :
    roundArc N visible k r x y ↔
      roundArc N visible l r (roundCountsEquiv agree N r x) (roundCountsEquiv agree N r y) := by
  rcases x with v | u | j <;> rcases y with w | z | i
  all_goals simp only [roundCountsEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.refl_apply, roundArc]
  · rw [leaving_congr agree r u.val u.property, demand_congr agree, supply_congr agree]
  · rw [leaving_congr agree r z.val z.property]

/-- Invisible count values are immaterial to the fixed-order certificate. -/
theorem Certificate.congr_counts {ell N t : ℕ} {H : Counting.FullHistory t} {k l : Counts}
    (cert : Certificate ell N t H k) (agree : CountsAgree (levels t H) k l) :
    Certificate ell N t H l := by
  refine ⟨cert.leaders_positive, cert.order_ge_leaders, ?_, ?_, ?_, ?_, cert.parent_visible,
    ?_, ?_, ?_, ?_⟩
  · intro r hr v hv
    rw [← agree r v hv]
    exact cert.positive r hr v hv
  · rw [← agree t H (by simp [levels_self])]
    exact cert.bottom_one
  · rw [← initialCount_congr agree]
    exact cert.initial_leaders
  · rw [← initialCount_congr agree]
    exact cert.initial_nonleaders
  · intro r hr u hu
    rw [← childCount_congr agree, ← agree r u hu]
    exact cert.refinement r hr u hu
  · intro r hr full u hu
    rw [← hidden_congr agree] at full
    rw [← supply_congr agree, ← demand_congr agree]
    exact cert.balance_full r hr full u hu
  · intro r hr proper u hu noLeaving
    rw [← hidden_congr agree] at proper
    rw [← leaving_congr agree r u hu] at noLeaving
    rw [← supply_congr agree, ← demand_congr agree]
    exact cert.balance_no_leaving r hr proper u hu noLeaving
  · intro r hr many
    exact (RealizabilityVerifier.connected_equiv (roundCountsEquiv agree N r) _ _
      (roundArc_counts_iff agree N r)).mp (cert.connected r hr many)

end Counting.Realizability
