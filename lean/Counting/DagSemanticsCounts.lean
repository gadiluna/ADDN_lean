import Counting.DagSemanticsStructure

namespace Counting.Executable

def Sparse (bundles : List (Nat × Nat)) : Prop :=
  bundles.Pairwise (fun a b => a.1 < b.1) ∧ ∀ edge ∈ bundles, 0 < edge.2

theorem sparse_of_countsSorted (bundles : List (Nat × Nat)) (sorted : countsSorted bundles = true) :
    Sparse bundles := by
  induction bundles with
  | nil => simp [Sparse]
  | cons edge rest ih =>
      simp only [countsSorted, Bool.and_eq_true, decide_eq_true_eq] at sorted
      have tail := ih sorted.2
      refine ⟨List.pairwise_cons.mpr ⟨?_, tail.1⟩, ?_⟩
      · cases rest with
        | nil => simp
        | cons next tailNodes =>
            have first : edge.1 < next.1 := by simpa using sorted.1.2
            intro other ho
            rcases List.mem_cons.mp ho with rfl | ho
            · exact first
            · exact first.trans ((List.pairwise_cons.mp tail.1).1 other ho)
      · intro other ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact sorted.1.1
        · exact tail.2 other ho

def bundleCount (key : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (i, c) :: rest => (if i = key then c else 0) + bundleCount key rest

theorem bundleCount_zero (key : Nat) (bundles : List (Nat × Nat))
    (absent : ∀ edge ∈ bundles, edge.1 ≠ key) : bundleCount key bundles = 0 := by
  induction bundles with
  | nil => rfl
  | cons edge rest ih =>
      simp only [bundleCount, if_neg (absent edge (by simp)), zero_add]
      exact ih (fun e he => absent e (by simp [he]))

theorem bundleCount_head (key count : Nat) (rest : List (Nat × Nat))
    (sparse : Sparse ((key, count) :: rest)) :
    bundleCount key ((key, count) :: rest) = count := by
  have absent : ∀ edge ∈ rest, edge.1 ≠ key := by
    intro edge he
    exact Nat.ne_of_gt ((List.pairwise_cons.mp sparse.1).1 edge he)
  simp only [bundleCount, if_true, bundleCount_zero key rest absent, add_zero]

theorem sparse_tail (edge : Nat × Nat) (rest : List (Nat × Nat))
    (sparse : Sparse (edge :: rest)) : Sparse rest :=
  ⟨(List.pairwise_cons.mp sparse.1).2, fun e he => sparse.2 e (by simp [he])⟩

/-- Sorted positive binary counts uniquely represent their expanded multiset. -/
theorem sparse_eq_of_counts (left right : List (Nat × Nat))
    (leftSparse : Sparse left) (rightSparse : Sparse right)
    (counts : ∀ key, bundleCount key left = bundleCount key right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons edge rest =>
          have positive := rightSparse.2 edge (by simp)
          have zero := counts edge.1
          rw [bundleCount_head _ _ _ rightSparse] at zero
          change 0 = edge.2 at zero
          omega
  | cons edge rest ih =>
      rcases edge with ⟨i, c⟩
      cases right with
      | nil =>
          have positive := leftSparse.2 (i, c) (by simp)
          have zero := counts i
          rw [bundleCount_head _ _ _ leftSparse] at zero
          change c = 0 at zero
          omega
      | cons edge tail =>
          rcases edge with ⟨j, d⟩
          have keyEqual : i = j := by
            by_contra neq
            rcases lt_or_gt_of_ne neq with hij | hji
            · have absent : ∀ edge ∈ (j, d) :: tail, edge.1 ≠ i := by
                intro e he
                rcases List.mem_cons.mp he with rfl | he
                · exact Nat.ne_of_gt hij
                · exact Nat.ne_of_gt (hij.trans ((List.pairwise_cons.mp rightSparse.1).1 e he))
              have positive := leftSparse.2 (i, c) (by simp)
              have zero := counts i
              rw [bundleCount_head _ _ _ leftSparse, bundleCount_zero _ _ absent] at zero
              omega
            · have absent : ∀ edge ∈ (i, c) :: rest, edge.1 ≠ j := by
                intro e he
                rcases List.mem_cons.mp he with rfl | he
                · exact Nat.ne_of_gt hji
                · exact Nat.ne_of_gt (hji.trans ((List.pairwise_cons.mp leftSparse.1).1 e he))
              have positive := rightSparse.2 (j, d) (by simp)
              have zero := counts j
              rw [bundleCount_zero _ _ absent, bundleCount_head _ _ _ rightSparse] at zero
              omega
          subst j
          have countEqual : c = d := by
            simpa only [bundleCount_head _ _ _ leftSparse, bundleCount_head _ _ _ rightSparse] using counts i
          subst d
          congr 1
          apply ih tail (sparse_tail _ _ leftSparse) (sparse_tail _ _ rightSparse)
          intro key
          have h := counts key
          simp only [bundleCount] at h
          exact Nat.add_left_cancel h

theorem bundleMessages_count {α : Type} [DecidableEq α] (value : Nat → α)
    (key : Nat) (bundles : List (Nat × Nat))
    (separates : ∀ edge ∈ bundles, value edge.1 = value key ↔ edge.1 = key) :
    (bundleMessages value bundles).count (value key) = bundleCount key bundles := by
  induction bundles with
  | nil => simp [bundleMessages, bundleCount]
  | cons edge rest ih =>
      rw [bundleMessages_cons, Multiset.count_add, Multiset.count_replicate,
        ih (fun e he => separates e (by simp [he]))]
      have heq := separates edge (by simp)
      simp only [bundleCount, heq]

theorem bundleMessages_eq_implies_bundles_eq {α : Type} (value : Nat → α)
    (left right : List (Nat × Nat)) (leftSparse : Sparse left) (rightSparse : Sparse right)
    (injective : ∀ i ∈ left ++ right, ∀ j ∈ left ++ right, value i.1 = value j.1 → i.1 = j.1)
    (equal : bundleMessages value left = bundleMessages value right) : left = right := by
  classical
  apply sparse_eq_of_counts left right leftSparse rightSparse
  intro key
  by_cases present : ∃ edge ∈ left ++ right, edge.1 = key
  · obtain ⟨edge, he, rfl⟩ := present
    have separatesLeft : ∀ e ∈ left, value e.1 = value edge.1 ↔ e.1 = edge.1 := by
      intro e hm
      exact ⟨injective e (List.mem_append_left _ hm) edge he, fun h => congrArg value h⟩
    have separatesRight : ∀ e ∈ right, value e.1 = value edge.1 ↔ e.1 = edge.1 := by
      intro e hm
      exact ⟨injective e (List.mem_append_right _ hm) edge he, fun h => congrArg value h⟩
    simpa only [bundleMessages_count value edge.1 left separatesLeft,
      bundleMessages_count value edge.1 right separatesRight] using
      congrArg (Multiset.count (value edge.1)) equal
  · have absent : ∀ edge ∈ left ++ right, edge.1 ≠ key := by
      simpa only [not_exists, not_and] using present
    rw [bundleCount_zero key left (fun e he => absent e (List.mem_append_left _ he)),
      bundleCount_zero key right (fun e he => absent e (List.mem_append_right _ he))]

end Counting.Executable
