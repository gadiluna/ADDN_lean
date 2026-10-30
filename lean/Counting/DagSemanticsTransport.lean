import Counting.DagSemanticsAncestors
import Counting.ExecutableRefinementWeights

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

theorem level_decoding_injOn (vista : Vista) (valid : vista.valid = true) (r : Nat) :
    Set.InjOn (decodeNode vista r) ((levelNodes vista r).toFinset : Set Nat) := by
  intro i hi j hj equal
  have hi' := (mem_levelNodes vista r i).mp (List.mem_toFinset.mp hi)
  have hj' := (mem_levelNodes vista r j).mp (List.mem_toFinset.mp hj)
  exact decodeNode_injective vista valid r i j hi'.1 hj'.1 hi'.2 hj'.2 equal

theorem sum_decodedLevel {M : Type*} [AddCommMonoid M]
    (vista : Vista) (valid : vista.valid = true) (r : Nat) (f : Counting.FullHistory r → M) :
    (∑ H ∈ decodedLevel vista r, f H) =
      ((levelNodes vista r).map (fun i => f (decodeNode vista r i))).sum := by
  classical
  rw [decodedLevel, Finset.sum_image (level_decoding_injOn vista valid r)]
  exact List.sum_toFinset _ (levelNodes_nodup vista r)

theorem filter_decodedLevel (vista : Vista) (r : Nat) (P : Counting.FullHistory r → Prop)
    [DecidablePred P] :
    (decodedLevel vista r).filter P =
      ((levelNodes vista r).filter (fun i => decide (P (decodeNode vista r i)))).toFinset.image
        (decodeNode vista r) := by
  classical
  ext H
  simp only [decodedLevel, Finset.mem_filter, Finset.mem_image, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq]
  aesop

theorem card_filter_decodedLevel (vista : Vista) (valid : vista.valid = true) (r : Nat)
    (P : Counting.FullHistory r → Prop) [DecidablePred P] :
    ((decodedLevel vista r).filter P).card =
      ((levelNodes vista r).filter (fun i => decide (P (decodeNode vista r i)))).length := by
  classical
  rw [filter_decodedLevel, Finset.card_image_iff.mpr]
  · exact List.toFinset_card_of_nodup ((levelNodes_nodup vista r).filter _)
  · intro i hi j hj equal
    apply level_decoding_injOn vista valid r
    · exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hi)).1
    · exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hj)).1
    · exact equal

theorem sum_filter_decodedLevel {M : Type*} [AddCommMonoid M]
    (vista : Vista) (valid : vista.valid = true) (r : Nat)
    (P : Counting.FullHistory r → Prop) [DecidablePred P] (f : Counting.FullHistory r → M) :
    (∑ H ∈ (decodedLevel vista r).filter P, f H) =
      (((levelNodes vista r).filter (fun i => decide (P (decodeNode vista r i)))).map
        (fun i => f (decodeNode vista r i))).sum := by
  classical
  rw [filter_decodedLevel, Finset.sum_image]
  · exact List.sum_toFinset _ ((levelNodes_nodup vista r).filter _)
  · intro i hi j hj equal
    apply level_decoding_injOn vista valid r
    · exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hi)).1
    · exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hj)).1
    · exact equal

/-- This proof-only extension gives each visible history its stored weight.
It is not used by the local executable algorithm. -/
noncomputable def decodedWeight (vista : Vista) (weights : Array Nat)
    (r : Nat) (H : Counting.FullHistory r) : Nat := by
  classical
  exact if h : ∃ i ∈ levelNodes vista r, decodeNode vista r i = H then
    weights[h.choose]?.getD 0 else 0

theorem decodedWeight_decode (vista : Vista) (valid : vista.valid = true) (weights : Array Nat)
    (r i : Nat) (present : i ∈ levelNodes vista r) :
    decodedWeight vista weights r (decodeNode vista r i) = weights[i]?.getD 0 := by
  classical
  unfold decodedWeight
  have found : ∃ j ∈ levelNodes vista r, decodeNode vista r j = decodeNode vista r i := ⟨i, present, rfl⟩
  rw [dif_pos found]
  have same : found.choose = i := level_decoding_injOn vista valid r
    (List.mem_toFinset.mpr found.choose_spec.1) (List.mem_toFinset.mpr present) found.choose_spec.2
  rw [same]

theorem parent_decode_eq_iff (vista : Vista) (valid : vista.valid = true) (r old new : Nat)
    (oldPresent : old ∈ levelNodes vista r) (newPresent : new ∈ levelNodes vista (r + 1)) :
    parent r (decodeNode vista (r + 1) new) = decodeNode vista r old ↔
      (vista.node new).parent = some old := by
  have oldInfo := (mem_levelNodes vista r old).mp oldPresent
  have newInfo := (mem_levelNodes vista (r + 1) new).mp newPresent
  obtain ⟨p, hp, hpi, hpl, _, _, _⟩ :=
    nodeValid_positive vista new (nodeValid_of_valid vista valid new newInfo.1) (by omega)
  rw [parent_decode vista r new p hp]
  constructor
  · intro equal
    have same : p = old := decodeNode_injective vista valid r p old (hpi.trans newInfo.1)
      oldInfo.1 (by omega) oldInfo.2 equal
    exact hp.trans (congrArg some same)
  · intro equal
    exact congrArg (decodeNode vista r) (Option.some.inj (hp.symm.trans equal))

theorem decoded_children_filter (vista : Vista) (valid : vista.valid = true) (r old : Nat)
    (oldPresent : old ∈ levelNodes vista r) :
    (levelNodes vista (r + 1)).filter (fun i =>
      decide (parent r (decodeNode vista (r + 1) i) = decodeNode vista r old)) =
      children vista old (r + 1) := by
  classical
  unfold children
  apply List.filter_congr
  intro i hi
  simp only [parent_decode_eq_iff vista valid r old i oldPresent hi]
  by_cases equal : (vista.node i).parent = some old <;> simp [equal]

theorem decoded_children_card (vista : Vista) (valid : vista.valid = true) (r old : Nat)
    (oldPresent : old ∈ levelNodes vista r) :
    ((decodedLevel vista (r + 1)).filter (fun H => parent r H = decodeNode vista r old)).card =
      (children vista old (r + 1)).length := by
  classical
  rw [card_filter_decodedLevel vista valid, decoded_children_filter vista valid r old oldPresent]


theorem decoded_parent_visible (vista : Vista) (valid : vista.valid = true) (r : Nat)
    (H : Counting.FullHistory (r + 1)) (present : H ∈ decodedLevel vista (r + 1)) :
    parent r H ∈ decodedLevel vista r := by
  obtain ⟨i, inside, level, rfl⟩ := (mem_decodedLevel vista (r + 1) H).mp present
  obtain ⟨p, hp, hpi, hpl, _, _, _⟩ :=
    nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) (by omega)
  rw [parent_decode vista r i p hp]
  exact (mem_decodedLevel vista r _).mpr ⟨p, hpi.trans inside, by omega, rfl⟩

theorem levelNodes_nonempty_of_le (vista : Vista) (valid : vista.valid = true) (r : Nat)
    (within : r ≤ (vista.node vista.bottom).level) : (levelNodes vista r) ≠ [] := by
  have inside : vista.bottom < vista.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  obtain ⟨i, hi, li, _, _⟩ := ascend_decode vista valid r
    ((vista.node vista.bottom).level - r) vista.bottom inside (Nat.add_sub_of_le within).symm
  intro empty
  have present := (mem_levelNodes vista r i).mpr ⟨hi, li⟩
  rw [empty] at present
  contradiction

theorem sum_decoded_children (vista : Vista) (valid : vista.valid = true) (weights : Array Nat)
    (r old : Nat) (present : old ∈ levelNodes vista r) :
    (∑ H ∈ (decodedLevel vista (r + 1)).filter (fun H => parent r H = decodeNode vista r old),
      decodedWeight vista weights (r + 1) H) =
      ((children vista old (r + 1)).map (fun i => weights[i]?.getD 0)).sum := by
  classical
  rw [sum_filter_decodedLevel vista valid, decoded_children_filter vista valid r old present]
  apply congrArg List.sum
  apply List.map_congr_left
  intro child hc
  exact decodedWeight_decode vista valid weights (r + 1) child (List.mem_filter.mp hc).1

theorem decoded_descendants_card (vista : Vista) (valid : vista.valid = true) (r t old : Nat)
    (within : r ≤ t) (present : old ∈ levelNodes vista r) :
    ((decodedLevel vista t).filter (fun H => ancestor r t H = decodeNode vista r old)).card =
      ((levelNodes vista t).filter (fun i => ascend vista (t - r) i == some old)).length := by
  classical
  rw [card_filter_decodedLevel vista valid]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have oldInfo := (mem_levelNodes vista r old).mp present
  have newInfo := (mem_levelNodes vista t i).mp hi
  simp only [← ascend_eq_iff_ancestor vista valid r t i old within newInfo.1 newInfo.2 oldInfo.1 oldInfo.2]
  by_cases equal : ascend vista (t - r) i = some old <;> simp [equal]

end Counting.Executable
