import Counting.CountingSize

namespace Counting.Executable

/-- Sparse bundles store each predecessor index at most once. -/
theorem sparse_keys_nodup (bundles : List (Nat × Nat)) (sparse : Sparse bundles) :
    (bundles.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact sparse.1.imp (fun less => Nat.ne_of_lt less)

/-- Every incoming entry refers to a distinct node at the preceding level.
Thus storage counts entries, not the potentially huge multiplicities. -/
theorem incoming_length_le_previous (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (inside : i < vista.nodes.size) :
    (vista.node i).incoming.length ≤ (levelNodes vista ((vista.node i).level-1)).length := by
  classical
  by_cases zero : (vista.node i).level = 0
  · rw [(nodeValid_zero vista i (nodeValid_of_valid vista valid i inside) zero).2.2]
    simp
  · obtain ⟨_, _, _, _, _, sorted, incoming⟩ :=
      nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) zero
    have nodup := sparse_keys_nodup _ (sparse_of_countsSorted _ sorted)
    have subset : ((vista.node i).incoming.map Prod.fst).toFinset ⊆
        (levelNodes vista ((vista.node i).level-1)).toFinset := by
      intro old member
      obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      obtain ⟨bound, level⟩ := incoming edge present
      apply List.mem_toFinset.mpr
      simp only [levelNodes, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨bound.trans inside, by omega⟩
    have count := Finset.card_le_card subset
    simpa only [List.toFinset_card_of_nodup nodup,
      List.toFinset_card_of_nodup (levelNodes_nodup vista _), List.length_map] using count

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

theorem incoming_length_le_card (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (i : Nat) (inside : i < vista.nodes.size) :
    (vista.node i).incoming.length ≤ Fintype.card V :=
  (incoming_length_le_previous vista valid i inside).trans
    (levelNodes_length_le_card G leader t observer vista valid depth physical _)

/-- Total sparse message incidences in a physical DAG are at most
(t+1)n². This bounds the representation without expanding parallel arcs. -/
theorem incoming_entries_le (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer) :
    ((List.range vista.nodes.size).map (fun i => (vista.node i).incoming.length)).sum ≤
      (t+1) * Fintype.card V ^ 2 := by
  have entries := List.sum_le_sum (l := List.range vista.nodes.size)
    (f := fun i => (vista.node i).incoming.length) (g := fun _ => Fintype.card V)
    (fun i member => incoming_length_le_card G leader t observer vista valid depth physical i (List.mem_range.mp member))
  have nodes := nodes_size_le_depth_mul_card G leader t observer vista valid depth physical
  have multiplied := Nat.mul_le_mul_right (Fintype.card V) nodes
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul] at entries
  calc
    _ ≤ vista.nodes.size * Fintype.card V := entries
    _ ≤ ((t+1) * Fintype.card V) * Fintype.card V := multiplied
    _ = _ := by ring

end Counting.Executable
