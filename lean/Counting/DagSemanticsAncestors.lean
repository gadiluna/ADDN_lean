import Counting.DagSemanticsLabels

namespace Counting.Executable
open Counting.TimingProtocolLocal

theorem decodeNode_cast (vista : Vista) (a b : Nat) (equal : a = b) (i : Nat) :
    cast (congrArg Counting.FullHistory equal) (decodeNode vista a i) = decodeNode vista b i := by
  subst b
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ascend_decode (vista : Vista) (valid : vista.valid = true) (r d i : Nat)
    (inside : i < vista.nodes.size) (level : (vista.node i).level = r + d) :
    ∃ j, j < vista.nodes.size ∧ (vista.node j).level = r ∧ ascend vista d i = some j ∧
      decodeNode vista r j = blackAncestor r d (decodeNode vista (r + d) i) := by
  induction d generalizing i with
  | zero => exact ⟨i, inside, level, rfl, rfl⟩
  | succ d ih =>
      obtain ⟨p, hp, hpi, hpl, _, _, _⟩ :=
        nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) (by omega)
      obtain ⟨j, hj, lj, asc, hist⟩ := ih p (hpi.trans inside) (by omega)
      refine ⟨j, hj, lj, ?_, ?_⟩
      · simp only [ascend, hp, Option.bind_some, asc]
      · change decodeNode vista r j = blackAncestor r d (decodeNode vista (r + d + 1) i).1
        rw [show (decodeNode vista (r + d + 1) i).1 = decodeNode vista (r + d) p from
          parent_decode vista (r + d) i p hp]
        exact hist

theorem ascend_eq_iff_blackAncestor (vista : Vista) (valid : vista.valid = true) (r d i j : Nat)
    (inside : i < vista.nodes.size) (level : (vista.node i).level = r + d)
    (targetInside : j < vista.nodes.size) (targetLevel : (vista.node j).level = r) :
    ascend vista d i = some j ↔
      blackAncestor r d (decodeNode vista (r + d) i) = decodeNode vista r j := by
  obtain ⟨k, hk, lk, asc, hist⟩ := ascend_decode vista valid r d i inside level
  constructor
  · intro accepted
    have equal : k = j := Option.some.inj (asc.symm.trans accepted)
    exact hist.symm.trans (congrArg (decodeNode vista r) equal)
  · intro equal
    have same := decodeNode_injective vista valid r k j hk targetInside lk targetLevel (hist.trans equal)
    exact asc.trans (congrArg some same)

/-- Executable pointer traversal is exactly the intrinsic black ancestor,
including zero-distance and extreme-level anchors. -/
theorem ascend_eq_iff_ancestor (vista : Vista) (valid : vista.valid = true) (r t i j : Nat)
    (within : r ≤ t) (inside : i < vista.nodes.size) (level : (vista.node i).level = t)
    (targetInside : j < vista.nodes.size) (targetLevel : (vista.node j).level = r) :
    ascend vista (t - r) i = some j ↔
      ancestor r t (decodeNode vista t i) = decodeNode vista r j := by
  unfold ancestor
  rw [dif_pos within, decodeNode_cast vista t (r + (t - r))
    (Nat.add_sub_of_le within).symm i]
  exact ascend_eq_iff_blackAncestor vista valid r (t - r) i j inside
    (level.trans (Nat.add_sub_of_le within).symm) targetInside targetLevel

end Counting.Executable
