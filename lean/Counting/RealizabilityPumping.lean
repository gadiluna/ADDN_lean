import Counting.RealizabilityConstructionTransport
import Counting.RealizabilityNecessity

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

variable {ell N t : ℕ} {H : FullHistory t} {k : Counts}

theorem Certificate.selected_subset_initial (cert : Certificate ell N t H k) (r : ℕ) :
    cert.selected r ⊆ cert.selected 0 := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact (cert.selected_nested r).trans ih

theorem Certificate.total_le_initial (cert : Certificate ell N t H k) (r : ℕ) :
    (∑ u ∈ levels t H r, k r u) ≤ ∑ u ∈ levels t H 0, k 0 u := by
  rw [← cert.selected_card r, ← cert.selected_card 0]
  exact Finset.card_le_card (cert.selected_subset_initial r)

theorem initial_total_eq : (∑ u ∈ levels t H 0, k 0 u) =
    initialCount (levels t H) k true + initialCount (levels t H) k false := by
  classical
  letI : Fintype (FullHistory 0) := inferInstanceAs (Fintype Bool)
  calc
    _ = ∑ u : FullHistory 0, if u ∈ levels t H 0 then k 0 u else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = _ := by
      change (∑ b : Bool, if (b : FullHistory 0) ∈ levels t H 0 then k 0 b else 0) = _
      rw [Fintype.sum_bool]
      rfl

theorem Certificate.initial_total_positive (cert : Certificate ell N t H k) :
    0 < ∑ u ∈ levels t H 0, k 0 u := by
  obtain ⟨u, hu⟩ := levels_nonempty (H := H) 0 (Nat.zero_le t)
  exact lt_of_lt_of_le (cert.positive 0 (Nat.zero_le t) u hu)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hu)

theorem Certificate.hidden_positive_of_open (cert : Certificate ell N t H k)
    (openSupport : (∑ u ∈ levels t H 0, k 0 u) < N) (r : ℕ) :
    0 < hidden N (levels t H) k r := by
  have := cert.total_le_initial (r + 1)
  unfold hidden
  omega

noncomputable def openRoundEquiv (N N' : ℕ) (visible : Levels) (k : Counts) (r : ℕ)
    (old : 0 < hidden N visible k r) (new : 0 < hidden N' visible k r) :
    RoundVertex N visible k r ≃ RoundVertex N' visible k r :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
    (finCongr (by simp [outsideSize, old, new])))

theorem open_roundArc_iff (N N' : ℕ) (visible : Levels) (k : Counts) (r : ℕ)
    (old : 0 < hidden N visible k r) (new : 0 < hidden N' visible k r)
    (x y : RoundVertex N visible k r) :
    roundArc N' visible k r (openRoundEquiv N N' visible k r old new x)
      (openRoundEquiv N N' visible k r old new y) ↔ roundArc N visible k r x y := by
  rcases x with v | u | j <;> rcases y with w | z | i
  all_goals rfl

theorem open_round_connected (N N' : ℕ) (visible : Levels) (k : Counts) (r : ℕ)
    (old : 0 < hidden N visible k r) (new : 0 < hidden N' visible k r)
    (connected : StronglyConnected (roundArc N visible k r)) :
    StronglyConnected (roundArc N' visible k r) := by
  let e := openRoundEquiv N N' visible k r old new
  have liftPath : ∀ x y, Relation.ReflTransGen (roundArc N visible k r) x y →
      Relation.ReflTransGen (roundArc N' visible k r) (e x) (e y) := by
    intro x y path
    induction path with
    | refl => exact .refl
    | @tail y z p edge ih => exact ih.tail ((open_roundArc_iff N N' visible k r old new y z).mpr edge)
  intro x y
  simpa only [Equiv.apply_symm_apply] using liftPath (e.symm x) (e.symm y) (connected _ _)

/-- An open count certificate can be used at any new order with enough
initial leader/nonleader capacity and a nonempty outside set. All round
graphs and balance tests are transported, rather than assumed again. -/
theorem Certificate.at_open_order (cert : Certificate ell N t H k)
    (openSupport : (∑ u ∈ levels t H 0, k 0 u) < N)
    (N' : ℕ) (leaders : ell ≤ N')
    (ordinary : initialCount (levels t H) k false ≤ N' - ell)
    (newOpen : (∑ u ∈ levels t H 0, k 0 u) < N') : Certificate ell N' t H k where
  leaders_positive := cert.leaders_positive
  order_ge_leaders := leaders
  positive := cert.positive
  bottom_one := cert.bottom_one
  initial_leaders := cert.initial_leaders
  initial_nonleaders := ordinary
  parent_visible := cert.parent_visible
  refinement := cert.refinement
  balance_full := by
    intro r _ zero
    have := cert.total_le_initial (r + 1)
    unfold hidden at zero
    omega
  balance_no_leaving := by
    intro r before _ u hu noLeaving
    exact cert.balance_no_leaving r before (cert.hidden_positive_of_open openSupport r) u hu noLeaving
  connected := by
    intro r before _
    have newHidden : 0 < hidden N' (levels t H) k r := by
      have := cert.total_le_initial (r + 1)
      unfold hidden
      omega
    have oldMany : 1 < N := by have := cert.initial_total_positive; omega
    exact open_round_connected N N' (levels t H) k r
      (cert.hidden_positive_of_open openSupport r) newHidden (cert.connected r before oldMany)

/-- Adding initially unselected nonleaders preserves the exact certificate. -/
theorem Certificate.pump (cert : Certificate ell N t H k)
    (openSupport : (∑ u ∈ levels t H 0, k 0 u) < N) (extra : ℕ) :
    Certificate ell (N + extra) t H k := by
  apply cert.at_open_order openSupport (N + extra)
  · exact cert.order_ge_leaders.trans (Nat.le_add_right N extra)
  · exact cert.initial_nonleaders.trans (Nat.sub_le_sub_right (Nat.le_add_right N extra) ell)
  · omega

/-- The first guaranteed order needs only the leader budget and the
number of initially selected nonleaders, not the original population. -/
theorem Certificate.eventual (cert : Certificate ell N t H k)
    (openSupport : (∑ u ∈ levels t H 0, k 0 u) < N) (extra : ℕ) :
    Certificate ell (ell + initialCount (levels t H) k false + 1 + extra) t H k := by
  apply cert.at_open_order openSupport
  · omega
  · omega
  · rw [initial_total_eq]
    have := cert.initial_leaders
    omega

theorem Certificate.eventual_threshold_le (_cert : Certificate ell N t H k) (K : ℕ)
    (bounded : (∑ u ∈ levels t H 0, k 0 u) ≤ K) :
    ell + initialCount (levels t H) k false + 1 ≤ K + ell + 1 := by
  rw [initial_total_eq] at bounded
  omega

theorem actual_counts_open {V : Type} [Fintype V]
    (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ) (observer : V)
    (proper : causalSupport G 0 t observer ≠ Finset.univ) :
    (∑ u ∈ levels t (history G leader t observer) 0, selectedCounts G leader t observer 0 u) < Fintype.card V := by
  rw [selectedCounts_total G leader t observer 0 (Nat.zero_le t)]
  have neq : (supportAt G t observer 0).card ≠ Fintype.card V :=
    fun eq => proper ((Finset.card_eq_iff_eq_univ _).mp eq)
  exact lt_of_le_of_ne (Finset.card_le_univ _) neq

theorem pumped_certificate_of_actual {V : Type} [Fintype V]
    (G : ℕ → V → V → ℕ) (leader : V → Bool) {ell : ℕ} (valid : Admissible ell G leader)
    (t : ℕ) (observer : V) (proper : causalSupport G 0 t observer ≠ Finset.univ) (extra : ℕ) :
    Certificate ell (Fintype.card V + extra) t (history G leader t observer)
      (selectedCounts G leader t observer) :=
  (certificate_of_actual G leader valid t observer).pump (actual_counts_open G leader t observer proper) extra

end Counting.Realizability
