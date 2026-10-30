import Counting.DagSemanticsLabels

namespace Counting.Executable
open Counting.TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Any valid DAG denoting an actual history has at most one stored node per
physical agent at each level. No connectivity or leader-count assumption is
needed for this bound. -/
theorem levelNodes_length_le_card (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer) (r : Nat) :
    (levelNodes vista r).length ≤ Fintype.card V := by
  subst t
  rw [levelNodes_length_eq_visible_card vista valid]
  change (levels _ (decodeNode vista _ vista.bottom) r).card ≤ _
  rw [physical]
  by_cases within : r ≤ (vista.node vista.bottom).level
  · rw [levels_eq_image G leader _ r within observer]
    apply Finset.card_image_le.trans
    exact Finset.card_image_le.trans (Finset.card_le_univ _)
  · rw [levels_above _ r _ (by omega)]
    simp

theorem stored_level_le_bottom (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (inside : i < vista.nodes.size) :
    (vista.node i).level ≤ (vista.node vista.bottom).level := by
  have visible := stored_history_visible vista valid i inside
  by_contra above
  rw [levels_above _ _ _ (by omega)] at visible
  exact Finset.notMem_empty _ visible

/-- Every stored node has an actual physical representative, even if its
index is unrelated to any physical agent identity. -/
theorem stored_node_realized (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (i : Nat) (inside : i < vista.nodes.size) :
    ∃ v, decodeNode vista (vista.node i).level i = Counting.history G leader (vista.node i).level v := by
  classical
  subst t
  have visible := stored_history_visible vista valid i inside
  change decodeNode vista (vista.node i).level i ∈ levels _ (decodeNode vista _ vista.bottom) _ at visible
  rw [physical, levels_eq_image G leader _ _ (stored_level_le_bottom vista valid i inside) observer] at visible
  obtain ⟨node, _, equal⟩ := Finset.mem_image.mp visible
  exact ⟨node.out, equal.symm⟩

/-- Injecting each stored node into its (level, physical representative)
pair bounds the whole shared DAG, without expanding histories into trees. -/
theorem nodes_size_le_depth_mul_card (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer) :
    vista.nodes.size ≤ (t+1) * Fintype.card V := by
  classical
  have represented : ∀ i : Fin vista.nodes.size,
      ∃ v, decodeNode vista (vista.node i.val).level i.val = Counting.history G leader (vista.node i.val).level v :=
    fun i => stored_node_realized G leader t observer vista valid depth physical i.val i.isLt
  choose agent histories using represented
  let position (i : Fin vista.nodes.size) : Fin (t+1) × V :=
    (⟨(vista.node i.val).level, by have := stored_level_le_bottom vista valid i.val i.isLt; omega⟩, agent i)
  have injective : Function.Injective position := by
    intro i j same
    have level : (vista.node i.val).level = (vista.node j.val).level :=
      congrArg (fun p : Fin (t+1) × V => p.1.val) same
    have agents : agent i = agent j := congrArg Prod.snd same
    apply Fin.ext
    apply decodeNode_injective vista valid (vista.node i.val).level i.val j.val i.isLt j.isLt rfl level.symm
    have equal := histories j
    rw [← level, ← agents] at equal
    exact (histories i).trans equal.symm
  have bound := Fintype.card_le_of_injective position injective
  simpa only [Fintype.card_fin, Fintype.card_prod] using bound

end Counting.Executable
