import Counting.HardnessVisibleLeader

namespace Counting.HardnessVisible
open DirectedCounting PaperHistory TimingProtocolLocal HardnessPath HardnessBaseline
open scoped BigOperators Classical

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)
variable {q m : Nat} (inst : X3C.Instance q m)

noncomputable def groupUnion : Finset V := by
  classical
  exact Finset.univ.biUnion (group G leader inst)

@[simp] theorem mem_groupUnion (v : V) :
    v ∈ groupUnion G leader inst ↔ ∃ i, v ∈ group G leader inst i := by
  classical
  simp [groupUnion]

theorem groupUnion_card (large : 2 ≤ q) :
    (groupUnion G leader inst).card = ∑ i, (group G leader inst i).card := by
  classical
  exact Finset.card_biUnion (fun i _ j _ different => groups_disjoint G leader inst large i j different)

theorem groupUnion_receipts (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (∑ v ∈ groupUnion G leader inst, G 1 observer v) =
      ∑ i, inst.coefficient i * (group G leader inst i).card := by
  classical
  rw [groupUnion, Finset.sum_biUnion (fun i _ j _ different => groups_disjoint G leader inst large i j different)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_congr rfl (fun v member => group_receipt G leader inst network observer same i v member)]
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem group_weighted_bound (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (∑ i, inst.coefficient i * (group G leader inst i).card) ≤ inst.weightedTarget := by
  rw [← groupUnion_receipts G leader inst large network observer same, ← observer_degree G leader inst observer same]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem first_represented_partition (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    HardnessExhaustive.represented G leader (X3C.base q) observer 1 =
      insert observer (groupUnion G leader inst) := by
  classical
  ext v
  rw [mem_represented_iff G leader _ _ _ (by unfold X3C.base; omega), same,
    baseline_level_mem_iff inst 1 (by unfold X3C.base; omega), Finset.mem_insert, mem_groupUnion]
  constructor
  · rintro (leading | ⟨i, p, member⟩)
    · exact Or.inl ((unique_observer G leader inst network observer same v).mp (congrArg Prod.fst leading))
    · exact Or.inr ⟨i, (mem_group G leader inst i v).mpr ⟨p, member⟩⟩
  · rintro (rfl | ⟨i, member⟩)
    · exact Or.inl (observer_first_history G leader inst v same)
    · obtain ⟨p, equal⟩ := (mem_group G leader inst i v).mp member
      exact Or.inr ⟨i, p, equal⟩

theorem observer_not_groupUnion (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    observer ∉ groupUnion G leader inst := by
  intro member
  obtain ⟨i, member⟩ := (mem_groupUnion G leader inst observer).mp member
  have nonleader := group_nonleader G leader inst i observer member
  rw [observer_leader G leader inst observer same] at nonleader
  cases nonleader

theorem first_represented_card (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (HardnessExhaustive.represented G leader (X3C.base q) observer 1).card =
      X3C.groupOrder (fun i => (group G leader inst i).card) := by
  rw [first_represented_partition G leader inst network observer same,
    Finset.card_insert_of_notMem (observer_not_groupUnion G leader inst observer same), groupUnion_card G leader inst large]
  exact Nat.add_comm _ _

/-- The shifted inequality, unlike the later equation, does not require
exhaustiveness. All coefficients are at least K and A<(q+1)K. -/
theorem shifted_excess_bound (large : 2 ≤ q) (a : Option (Fin m) → Nat)
    (lower : ∀ i, X3C.base q ≤ a i)
    (weighted : (∑ i, inst.coefficient i * a i) ≤ inst.weightedTarget) :
    (∑ i, (a i - X3C.base q)) ≤ q := by
  have shifted := inst.shifted_sum a lower
  have excess : (∑ i, inst.coefficient i * (a i-X3C.base q)) ≤ X3C.target q := by
    unfold X3C.Instance.weightedTarget at weighted
    omega
  have highLower : X3C.high q * (∑ i, (a i-X3C.base q)) ≤
      ∑ i, inst.coefficient i * (a i-X3C.base q) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (inst.coefficient_gt_high large i).le)
  have targetUpper := X3C.target_lt q
  have positive := X3C.high_positive q
  nlinarith

theorem first_represented_upper (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (HardnessExhaustive.represented G leader (X3C.base q) observer 1).card ≤ X3C.baselineMass q m+q := by
  rw [first_represented_card G leader inst large network observer same,
    X3C.groupOrder_shifted _ (group_lower G leader inst observer same)]
  exact Nat.add_le_add_left
    (shifted_excess_bound inst large _ (group_lower G leader inst observer same)
      (group_weighted_bound G leader inst large network observer same)) _

/-- The first visible level in every one-leader realization of the baseline
vista is exhaustive. Both endpoint bounds are derived from the actual vista. -/
theorem first_level_exhaustive (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    HardnessExhaustive.represented G leader (X3C.base q) observer 1 = Finset.univ ∧
      CoreTiming.levelsAt G leader (X3C.base q) observer 1 = Finset.univ :=
  HardnessExhaustive.first_visible_level_exhaustive G leader (X3C.base q) observer (X3C.base q) q
    (X3C.baselineMass q m) rfl (by omega) network.connected
    (first_represented_upper G leader inst large network observer same)
    (final_represented_lower G leader inst large observer same)

end Counting.HardnessVisible
