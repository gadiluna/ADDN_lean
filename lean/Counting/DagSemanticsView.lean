import Counting.DagSemanticsVisibility

namespace Counting.Executable
open Counting.TimingProtocolLocal

theorem stored_levels_subset_bottom (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (inside : i < vista.nodes.size) (r : Nat) :
    levels (vista.node i).level (decodeNode vista (vista.node i).level i) r ⊆
      levels (vista.node vista.bottom).level vista.denotes r := by
  have all := valid_nodes_induction vista valid (fun i => ∀ r,
    levels (vista.node i).level (decodeNode vista (vista.node i).level i) r ⊆
      levels (vista.node vista.bottom).level vista.denotes r) (by intro r; exact Finset.Subset.refl _)
    (by
      intro j hj seen p hp r
      have nonzero : (vista.node j).level ≠ 0 := by
        intro hz
        have hn := (nodeValid_zero vista j (nodeValid_of_valid vista valid j hj) hz).1
        rw [hn] at hp
        contradiction
      obtain ⟨q, hq, _, level, _, _, _⟩ :=
        nodeValid_positive vista j (nodeValid_of_valid vista valid j hj) nonzero
      have heq : q = p := Option.some.inj (hq.symm.trans hp)
      subst q
      apply Finset.Subset.trans ?_ (seen r)
      rw [← level]
      have parentHistory : (decodeNode vista ((vista.node p).level + 1) j).1 =
          decodeNode vista (vista.node p).level p := by
        simp only [decodeNode, hp, Option.getD_some]
      simpa only [parentHistory] using levels_parent_subset (vista.node p).level r
        (decodeNode vista ((vista.node p).level + 1) j))
    (by
      intro j hj seen edge he r
      have nonzero : (vista.node j).level ≠ 0 := by
        intro hz
        have hn := (nodeValid_zero vista j (nodeValid_of_valid vista valid j hj) hz).2.2
        rw [hn] at he
        contradiction
      obtain ⟨_, _, _, _, _, sorted, incoming⟩ :=
        nodeValid_positive vista j (nodeValid_of_valid vista valid j hj) nonzero
      have level := (incoming edge he).2
      have positive := (sparse_of_countsSorted _ sorted).2 edge he
      have member : decodeNode vista (vista.node edge.1).level edge.1 ∈
          (decodeNode vista ((vista.node edge.1).level + 1) j).2.2 := by
        exact (mem_bundleMessages _ _ _).mpr ⟨edge, he, positive, rfl⟩
      apply Finset.Subset.trans ?_ (seen r)
      rw [← level]
      exact levels_message_subset (vista.node edge.1).level r _ _ member)
  exact all i inside r

theorem stored_history_visible (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (inside : i < vista.nodes.size) :
    decodeNode vista (vista.node i).level i ∈
      levels (vista.node vista.bottom).level vista.denotes (vista.node i).level := by
  apply stored_levels_subset_bottom vista valid i inside (vista.node i).level
  simp only [levels_self, Finset.mem_singleton]

theorem visible_history_stored (vista : Vista) (valid : vista.valid = true)
    (depth i : Nat) (inside : i < vista.nodes.size) (level : (vista.node i).level = depth)
    (r : Nat) (H : Counting.FullHistory r)
    (visible : H ∈ levels depth (decodeNode vista depth i) r) : H ∈ decodedLevel vista r := by
  induction depth generalizing i with
  | zero =>
      have rzero : r = 0 := by
        by_contra hn
        rw [levels_above 0 r _ (by omega)] at visible
        exact Finset.notMem_empty H visible
      subst r
      have heq : H = decodeNode vista 0 i := by simpa only [levels_self, Finset.mem_singleton] using visible
      exact (mem_decodedLevel _ _ _).mpr ⟨i, inside, level, heq.symm⟩
  | succ depth ih =>
      by_cases rtop : r = depth + 1
      · subst r
        have heq : H = decodeNode vista (depth + 1) i := by
          simpa only [levels_self, Finset.mem_singleton] using visible
        exact (mem_decodedLevel _ _ _).mpr ⟨i, inside, level, heq.symm⟩
      have below : r ≤ depth := by
        by_contra hn
        have above : depth + 1 < r := by omega
        rw [levels_above (depth + 1) r _ above] at visible
        exact Finset.notMem_empty H visible
      obtain ⟨p, hp, hpi, hpl, _, _, incoming⟩ :=
        nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) (by omega)
      rw [levels_succ_of_le depth r _ below] at visible
      rcases Finset.mem_union.mp visible with own | message
      · apply ih p (hpi.trans inside) (by omega)
        simpa only [decodeNode, hp, Option.getD_some] using own
      · obtain ⟨M, member, occurs⟩ := Finset.mem_biUnion.mp message
        obtain ⟨edge, he, _, equal⟩ := (mem_bundleMessages _ _ _).mp (Multiset.mem_toFinset.mp member)
        obtain ⟨hei, hel⟩ := incoming edge he
        apply ih edge.1 (hei.trans inside) (by omega)
        simpa only [equal] using occurs

/-- The finite stored levels are precisely the intrinsic visible histories;
the two directions exclude missing and extraneous nodes respectively. -/
theorem decodedLevel_eq_levels (vista : Vista) (valid : vista.valid = true) (r : Nat) :
    decodedLevel vista r = levels (vista.node vista.bottom).level vista.denotes r := by
  classical
  ext H
  constructor
  · intro h
    obtain ⟨i, inside, level, equal⟩ := (mem_decodedLevel _ _ _).mp h
    have seen := stored_history_visible vista valid i inside
    rw [level, equal] at seen
    exact seen
  · intro h
    have inside : vista.bottom < vista.nodes.size := by
      simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      exact valid.1.1.1
    exact visible_history_stored vista valid (vista.node vista.bottom).level vista.bottom inside rfl r H h

/-- Stored node counts are unchanged by the semantic interpretation. -/
theorem levelNodes_length_eq_visible_card (vista : Vista) (valid : vista.valid = true) (r : Nat) :
    (levelNodes vista r).length =
      (levels (vista.node vista.bottom).level vista.denotes r).card := by
  classical
  rw [← decodedLevel_eq_levels vista valid]
  unfold decodedLevel
  rw [Finset.card_image_iff.mpr]
  · exact (List.toFinset_card_of_nodup (levelNodes_nodup vista r)).symm
  · intro i hi j hj equal
    have hi' : i < vista.nodes.size ∧ (vista.node i).level = r := by
      simpa only [Finset.mem_coe, List.mem_toFinset, levelNodes, List.mem_filter,
        List.mem_range, beq_iff_eq] using hi
    have hj' : j < vista.nodes.size ∧ (vista.node j).level = r := by
      simpa only [Finset.mem_coe, List.mem_toFinset, levelNodes, List.mem_filter,
        List.mem_range, beq_iff_eq] using hj
    exact decodeNode_injective vista valid r i j hi'.1 hj'.1 hi'.2 hj'.2 equal

end Counting.Executable
