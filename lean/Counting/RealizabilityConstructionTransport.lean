import Counting.RealizabilityConstructionAllocation
import Counting.RealizabilityConstructionConnected

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal RealizabilityConstruction

variable {ell N t : ℕ} {H : FullHistory t} {k : Counts}

theorem occurrences_nonempty (r d : ℕ) (H : FullHistory (r + d)) :
    (occurrences r d H).Nonempty := by
  induction d with
  | zero => exact Finset.singleton_nonempty H
  | succ d ih => exact (ih H.1).mono Finset.subset_union_left

theorem levels_nonempty (r : ℕ) (within : r ≤ t) : (levels t H r).Nonempty := by
  unfold levels
  rw [dif_pos within]
  exact occurrences_nonempty _ _ _

theorem Certificate.round_center_some_iff (cert : Certificate ell N t H k) (r : ℕ) :
    (cert.roundData r).center.isSome = true ↔ 0 < hidden N (levels t H) k r := by
  have iff := cert.round_center_none_iff r
  cases hc : (cert.roundData r).center with
  | none => simp only [hc, true_iff] at iff; simp [iff]
  | some a => simp only [hc, Option.some_ne_none, false_iff] at iff; simpa [hc] using Nat.pos_of_ne_zero iff

theorem Certificate.round_leaver_some_iff (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    ((cert.roundData r).leaver u).isSome = true ↔ 0 < leaving (levels t H) k r u.val := by
  have iff := cert.round_leaver_none_iff r u
  cases hc : (cert.roundData r).leaver u with
  | none => simp only [hc, true_iff] at iff; simp [iff]
  | some a => simp only [hc, Option.some_ne_none, false_iff] at iff; simpa [hc] using Nat.pos_of_ne_zero iff

noncomputable def Certificate.outsideEquiv (cert : Certificate ell N t H k) (r : ℕ) :
    Fin (outsideSize N (levels t H) k r) ≃ (cert.roundData r).OutsideVertex where
  toFun j := ⟨(), (cert.round_center_some_iff r).mpr (by
    have hj := j.isLt
    by_contra hn
    simp [outsideSize, hn] at hj)⟩
  invFun x := ⟨0, by
    have hp := (cert.round_center_some_iff r).mp x.property
    simp [outsideSize, hp]⟩
  left_inv j := by
    apply Fin.ext
    change 0 = j.val
    have hj := j.isLt
    unfold outsideSize at hj
    split at hj <;> omega
  right_inv x := by
    apply Subtype.ext
    exact Unit.ext _ _

noncomputable def Certificate.typeEquiv (cert : Certificate ell N t H k) (r : ℕ) :
    RoundVertex N (levels t H) k r ≃ (cert.roundData r).TypeVertex :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (cert.outsideEquiv r))

theorem Certificate.typeArc_iff (cert : Certificate ell N t H k) (r : ℕ)
    (x y : RoundVertex N (levels t H) k r) :
    (cert.roundData r).typeArc (cert.typeEquiv r x) (cert.typeEquiv r y) ↔
      roundArc N (levels t H) k r x y := by
  rcases x with v | u | j <;> rcases y with w | z | i
  all_goals simp only [Certificate.typeEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
    RoundData.typeArc, roundArc]
  · change (cert.nodeParent r v = z ∧ 0 < degree r v.val) ↔ _
    simp only [Subtype.ext_iff, Certificate.nodeParent_val]
  · rfl
  · rw [cert.round_leaver_some_iff, cert.round_demand, cert.round_supply]
  · exact cert.round_leaver_some_iff r z

theorem Certificate.type_connected (cert : Certificate ell N t H k) (r : ℕ)
    (before : r < t) (many : 1 < N) : StronglyConnected (cert.roundData r).typeArc := by
  have liftPath : ∀ x y, Relation.ReflTransGen (roundArc N (levels t H) k r) x y →
      Relation.ReflTransGen (cert.roundData r).typeArc (cert.typeEquiv r x) (cert.typeEquiv r y) := by
    intro x y path
    induction path with
    | refl => exact .refl
    | @tail y z p edge ih => exact ih.tail ((cert.typeArc_iff r y z).mpr edge)
  intro x y
  simpa using liftPath (cert.typeEquiv r |>.symm x) (cert.typeEquiv r |>.symm y)
    (cert.connected r before many _ _)

theorem Certificate.new_type_represented (cert : Certificate ell N t H k) (r : ℕ)
    (before : r < t) (v : VisibleNode (levels t H) (r + 1)) :
    ∃ a, (cert.roundData r).new a = some v := by
  obtain ⟨a, ha⟩ := cert.group_nonempty (r + 1) (by omega) v
  exact ⟨a, (cert.tag_some_iff (r + 1) a v).mpr ha⟩

/-- The actual compact certificate guarantees strong connectivity of the
expanded physical graph used in the constructive realization. -/
theorem Certificate.expanded_connected (cert : Certificate ell N t H k) (r : ℕ)
    (before : r < t) (many : 1 < N) :
    StronglyConnected (fun x y => 0 < (cert.roundData r).expanded x y) := by
  letI : Nonempty (VisibleNode (levels t H) r) :=
    ⟨⟨(levels_nonempty (H := H) r (by omega)).choose, (levels_nonempty (H := H) r (by omega)).choose_spec⟩⟩
  letI : Nonempty (VisibleNode (levels t H) (r + 1)) :=
    ⟨⟨(levels_nonempty (H := H) (r + 1) (by omega)).choose,
      (levels_nonempty (H := H) (r + 1) (by omega)).choose_spec⟩⟩
  exact (cert.roundData r).expanded_connected (cert.new_type_represented r before) (cert.type_connected r before many)

end Counting.Realizability
