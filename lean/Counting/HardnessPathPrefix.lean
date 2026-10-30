import Counting.HardnessPathHistories

namespace Counting.HardnessPath

variable {I : Type} [Fintype I]

noncomputable def pathNetwork (coeff size : I → Nat) : Nat → Agent size → Agent size → Nat :=
  fun _ => edge coeff size

/-- Physical paths realize the canonical histories through every round
strictly smaller than each group length. The only global numerical datum
in the histories is the leader's common weighted outdegree C. -/
theorem path_histories (coeff size : I → Nat) (C : Nat)
    (weighted : (∑ i, coeff i * size i) = C) (r : Nat)
    (lengths : ∀ i, r < size i) :
    history (pathNetwork coeff size) (leader size) r none = leaderHistory coeff C r ∧
      ∀ (i : I) (j : Fin (size i)),
        history (pathNetwork coeff size) (leader size) r (some ⟨i, j⟩) =
          memberHistory coeff C r i j.val := by
  induction r with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ r ih =>
      obtain ⟨oldLeader, oldMembers⟩ := ih (fun i => by have := lengths i; omega)
      have positive : ∀ i, 0 < size i := fun i => by have := lengths i; omega
      constructor
      · rw [history, leaderHistory_succ]
        refine Prod.ext oldLeader (Prod.ext ?_ ?_)
        · exact (leader_outdegree coeff size).trans weighted
        · rw [show pathNetwork coeff size (r + 1) = edge coeff size from rfl,
            incoming_leader coeff size positive]
          apply Finset.sum_congr rfl
          intro i _
          rw [oldMembers]
          congr 1
          apply member_suffix
          dsimp [last]
          have := lengths i
          omega
      · intro i j
        rw [history, memberHistory_succ]
        refine Prod.ext (oldMembers i j) (Prod.ext ?_ ?_)
        · exact member_outdegree coeff size ⟨i, j⟩
        · change incoming (edge coeff size)
            (history (pathNetwork coeff size) (leader size) r) (some ⟨i, j⟩) = _
          by_cases first : j.val = 0
          · rw [incoming_first coeff size _ i j first, oldLeader, first]
            exact (add_zero _).symm
          · let prev : Fin (size i) := ⟨j.val - 1, by omega⟩
            have consecutive : prev.val + 1 = j.val := by dsimp [prev]; omega
            rw [incoming_next coeff size _ i prev j consecutive, oldLeader, oldMembers]
            rw [← consecutive]

/-- The exact physical partition, including nonempty terminal suffixes. -/
theorem physical_member_partition (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (lengths : ∀ i, r < size i)
    (i j : I) (p : Fin (size i)) (q : Fin (size j)) :
    history (pathNetwork coeff size) (leader size) r (some ⟨i, p⟩) =
      history (pathNetwork coeff size) (leader size) r (some ⟨j, q⟩) ↔
        i = j ∧ min p.val r = min q.val r := by
  rw [(path_histories coeff size C weighted r lengths).2,
    (path_histories coeff size C weighted r lengths).2]
  exact member_partition coeff distinct C r positive i j p.val q.val

/-- The leader's entire history is independent of the physical group lengths. -/
theorem common_leader_history (coeff left right : I → Nat) (C r : Nat)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i) :
    history (pathNetwork coeff left) (leader left) r none =
      history (pathNetwork coeff right) (leader right) r none :=
  (path_histories coeff left C leftWeight r leftLength).1.trans
    (path_histories coeff right C rightWeight r rightLength).1.symm

/-- Matching a singleton position or the suffix class gives exactly equal
histories across two physical populations. -/
theorem common_member_history (coeff left right : I → Nat) (C r : Nat)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i)
    (i : I) (p : Fin (left i)) (q : Fin (right i))
    (position : min p.val r = min q.val r) :
    history (pathNetwork coeff left) (leader left) r (some ⟨i, p⟩) =
      history (pathNetwork coeff right) (leader right) r (some ⟨i, q⟩) := by
  rw [(path_histories coeff left C leftWeight r leftLength).2,
    (path_histories coeff right C rightWeight r rightLength).2]
  exact (member_eq_iff_min coeff C r i p.val q.val).mpr position

theorem physical_member_ne_leader (coeff size : I → Nat) (C r : Nat)
    (weighted : (∑ i, coeff i * size i) = C) (lengths : ∀ i, r < size i)
    (i : I) (p : Fin (size i)) :
    history (pathNetwork coeff size) (leader size) r (some ⟨i, p⟩) ≠
      history (pathNetwork coeff size) (leader size) r none := by
  rw [(path_histories coeff size C weighted r lengths).1,
    (path_histories coeff size C weighted r lengths).2]
  exact member_ne_leader coeff C r i p.val

theorem history_range_subset (coeff left right : I → Nat) (C r : Nat)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i) :
    Set.range (history (pathNetwork coeff left) (leader left) r) ⊆
      Set.range (history (pathNetwork coeff right) (leader right) r) := by
  rintro H ⟨a, rfl⟩
  cases a with
  | none =>
      exact ⟨none, (common_leader_history coeff left right C r leftWeight rightWeight
        leftLength rightLength).symm⟩
  | some a =>
      obtain ⟨i, p⟩ := a
      let position : Fin (right i) := ⟨min p.val r, (min_le_right _ _).trans_lt (rightLength i)⟩
      refine ⟨some ⟨i, position⟩, (common_member_history coeff left right C r leftWeight rightWeight
        leftLength rightLength i p position ?_).symm⟩
      dsimp [position]
      simp only [min_assoc, min_self]

/-- Histories are canonical node labels carrying parent, degree and incoming
multiset labels. Equality of their realized sets therefore identifies the
entire labeled level, rather than merely a chosen observer's history. -/
theorem history_range_eq (coeff left right : I → Nat) (C r : Nat)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i) :
    Set.range (history (pathNetwork coeff left) (leader left) r) =
      Set.range (history (pathNetwork coeff right) (leader right) r) :=
  Set.Subset.antisymm
    (history_range_subset coeff left right C r leftWeight rightWeight leftLength rightLength)
    (history_range_subset coeff right left C r rightWeight leftWeight rightLength leftLength)

/-- The common prefix through round B-1, including the initial level. -/
theorem common_path_prefix (coeff left right : I → Nat) (C B : Nat) (positive : 0 < B)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, B ≤ left i) (rightLength : ∀ i, B ≤ right i) :
    ∀ r, r ≤ B - 1 →
      Set.range (history (pathNetwork coeff left) (leader left) r) =
        Set.range (history (pathNetwork coeff right) (leader right) r) := by
  intro r within
  exact history_range_eq coeff left right C r leftWeight rightWeight
    (fun i => by have := leftLength i; omega) (fun i => by have := rightLength i; omega)

end Counting.HardnessPath
