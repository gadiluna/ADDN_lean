import Counting.DagSemanticsClosure
import Counting.TimingProtocolLocal

namespace Counting.Executable
open Counting.TimingProtocolLocal

theorem occurrences_cast_eq (r a b : Nat) (equal : a = b)
    (H : Counting.FullHistory (r + a)) :
    occurrences r b (cast (congrArg (fun d => Counting.FullHistory (r + d)) equal) H) =
      occurrences r a H := by
  subst b
  rfl

theorem levels_add (r d : Nat) (H : Counting.FullHistory (r + d)) :
    levels (r + d) H r = occurrences r d H := by
  unfold levels
  rw [dif_pos (Nat.le_add_right r d)]
  exact occurrences_cast_eq r d (r + d - r) (Nat.add_sub_cancel_left r d).symm H

@[simp] theorem levels_self (depth : Nat) (H : Counting.FullHistory depth) :
    levels depth H depth = {H} := by
  classical
  exact (levels_add depth 0 H).trans rfl

theorem levels_succ_of_le (depth r : Nat) (H : Counting.FullHistory (depth + 1)) (le : r ≤ depth) :
    levels (depth + 1) H r = levels depth H.1 r ∪
      H.2.2.toFinset.biUnion (fun h => levels depth h r) := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  change levels (r + (d + 1)) H r = _
  rw [levels_add]
  simp only [occurrences, levels_add]

theorem levels_above (depth r : Nat) (H : Counting.FullHistory depth) (above : depth < r) :
    levels depth H r = ∅ := by
  simp only [levels, dif_neg (Nat.not_le_of_gt above)]

theorem levels_parent_subset (depth r : Nat) (H : Counting.FullHistory (depth + 1)) :
    levels depth H.1 r ⊆ levels (depth + 1) H r := by
  by_cases le : r ≤ depth
  · rw [levels_succ_of_le depth r H le]
    exact Finset.subset_union_left
  · rw [levels_above depth r H.1 (Nat.lt_of_not_ge le)]
    exact Finset.empty_subset _

theorem levels_message_subset (depth r : Nat) (H : Counting.FullHistory (depth + 1))
    (message : Counting.FullHistory depth) (member : message ∈ H.2.2) :
    levels depth message r ⊆ levels (depth + 1) H r := by
  classical
  by_cases le : r ≤ depth
  · rw [levels_succ_of_le depth r H le]
    intro h hh
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨message, Multiset.mem_toFinset.mpr member, hh⟩)
  · rw [levels_above depth r message (Nat.lt_of_not_ge le)]
    exact Finset.empty_subset _

theorem mem_bundleMessages {α : Type} (value : Nat → α) (bundles : List (Nat × Nat)) (x : α) :
    x ∈ bundleMessages value bundles ↔ ∃ edge ∈ bundles, 0 < edge.2 ∧ value edge.1 = x := by
  induction bundles with
  | nil => simp
  | cons edge rest ih =>
      simp only [bundleMessages_cons, Multiset.mem_add, Multiset.mem_replicate, ih,
        List.mem_cons, exists_eq_or_imp]
      simp only [Nat.pos_iff_ne_zero, eq_comm (a := x)]

noncomputable def decodedLevel (vista : Vista) (depth : Nat) : Finset (Counting.FullHistory depth) := by
  classical
  exact (levelNodes vista depth).toFinset.image (decodeNode vista depth)

theorem mem_decodedLevel (vista : Vista) (depth : Nat) (H : Counting.FullHistory depth) :
    H ∈ decodedLevel vista depth ↔ ∃ i, i < vista.nodes.size ∧
      (vista.node i).level = depth ∧ decodeNode vista depth i = H := by
  classical
  simp only [decodedLevel, Finset.mem_image, List.mem_toFinset, levelNodes,
    List.mem_filter, List.mem_range, beq_iff_eq]
  aesop

end Counting.Executable
