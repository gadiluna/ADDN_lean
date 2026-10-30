import Counting.DagSemanticsView

namespace Counting.Executable
open Counting.TimingProtocolLocal

def rootInput : (depth : Nat) → Counting.FullHistory depth → Bool
  | 0, H => H
  | depth + 1, H => rootInput depth H.1

theorem rootInput_cast (a b : Nat) (equal : a = b) (H : Counting.FullHistory a) :
    rootInput b (cast (congrArg Counting.FullHistory equal) H) = rootInput a H := by
  subst b
  rfl

theorem blackAncestor_zero_eq_rootInput (d : Nat) (H : Counting.FullHistory (0 + d)) :
    blackAncestor 0 d H = rootInput (0 + d) H := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih H.1

theorem input_eq_rootInput (depth : Nat) (H : Counting.FullHistory depth) :
    input depth H = rootInput depth H := by
  unfold input ancestor
  rw [dif_pos (Nat.zero_le depth), blackAncestor_zero_eq_rootInput]
  exact rootInput_cast depth (0 + (depth - 0)) (Nat.add_sub_of_le (Nat.zero_le depth)).symm H

theorem rootInput_decode (vista : Vista) (valid : vista.valid = true)
    (depth i : Nat) (inside : i < vista.nodes.size) (level : (vista.node i).level = depth) :
    rootInput depth (decodeNode vista depth i) = (vista.node i).leader := by
  induction depth generalizing i with
  | zero => rfl
  | succ depth ih =>
      obtain ⟨p, hp, hpi, hpl, leader, _, _⟩ :=
        nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) (by omega)
      simp only [rootInput, decodeNode, hp, Option.getD_some]
      exact (ih p (hpi.trans inside) (by omega)).trans leader

theorem input_decode (vista : Vista) (valid : vista.valid = true)
    (depth i : Nat) (inside : i < vista.nodes.size) (level : (vista.node i).level = depth) :
    input depth (decodeNode vista depth i) = (vista.node i).leader := by
  rw [input_eq_rootInput]
  exact rootInput_decode vista valid depth i inside level

theorem parent_decode (vista : Vista) (depth i p : Nat) (hp : (vista.node i).parent = some p) :
    parent depth (decodeNode vista (depth + 1) i) = decodeNode vista depth p := by
  simp only [parent, decodeNode, hp, Option.getD_some]

theorem degree_decode (vista : Vista) (depth i : Nat) :
    degree depth (decodeNode vista (depth + 1) i) = (vista.node i).degree := rfl

theorem lookup_eq_bundleCount (bundles : List (Nat × Nat)) (sparse : Sparse bundles) (key : Nat) :
    ((bundles.find? fun edge => edge.1 == key).map Prod.snd).getD 0 = bundleCount key bundles := by
  induction bundles with
  | nil => rfl
  | cons edge rest ih =>
      rcases edge with ⟨i, c⟩
      by_cases equal : i = key
      · subst i
        rw [bundleCount_head _ _ _ sparse]
        simp
      · have hb : (i == key) = false := beq_eq_false_iff_ne.mpr equal
        simp only [List.find?_cons, hb, equal, if_false, bundleCount, zero_add]
        exact ih (sparse_tail _ _ sparse)

theorem red_decode (vista : Vista) (valid : vista.valid = true)
    (depth old new : Nat) (oldInside : old < vista.nodes.size) (newInside : new < vista.nodes.size)
    (oldLevel : (vista.node old).level = depth) (newLevel : (vista.node new).level = depth + 1) :
    red depth (decodeNode vista depth old) (decodeNode vista (depth + 1) new) =
      countFrom (vista.node new) old := by
  classical
  obtain ⟨_, _, _, _, _, sorted, incoming⟩ :=
    nodeValid_positive vista new (nodeValid_of_valid vista valid new newInside) (by omega)
  change (bundleMessages (decodeNode vista depth) (vista.node new).incoming).count
    (decodeNode vista depth old) = _
  rw [bundleMessages_count (decodeNode vista depth) old (vista.node new).incoming]
  · exact (lookup_eq_bundleCount _ (sparse_of_countsSorted _ sorted) old).symm
  · intro edge he
    obtain ⟨hei, hel⟩ := incoming edge he
    exact ⟨decodeNode_injective vista valid depth edge.1 old (hei.trans newInside) oldInside
      (by omega) oldLevel, fun h => congrArg (decodeNode vista depth) h⟩

end Counting.Executable
