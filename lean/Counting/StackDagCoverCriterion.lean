import Counting.StackDagCoverSpec
import Counting.DagClosureCriterion

namespace Counting.StackMachine.DagValidation
open Executable

theorem noNodeReference_false_iff (target : Nat) (node : Node) :
    noNodeReference target node=false ↔
      node.parent=some target ∨ ∃ edge∈node.incoming,edge.1=target := by
  simp [noNodeReference,noIncomingReference]
  tauto

theorem noTableReference_false_iff (target : Nat) (vista : Vista) :
    noTableReference target vista.nodes.toList=false ↔
      ∃ source,source < vista.nodes.size ∧ DagReference vista source target := by
  simp only [noTableReference,List.all_eq_false,Bool.not_eq_true,noNodeReference_false_iff]
  constructor
  · rintro ⟨node,member,reference⟩
    obtain ⟨source,inside,rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    exact ⟨source,inside,by
      simpa only [DagReference,Vista.node,Array.getElem?_eq_getElem inside,Option.getD_some] using reference⟩
  · rintro ⟨source,inside,reference⟩
    refine ⟨vista.nodes[source],Array.mem_toList_iff.mpr (Array.getElem_mem inside),?_⟩
    simpa only [DagReference,Vista.node,Array.getElem?_eq_getElem inside,Option.getD_some] using reference

/-- The runtime scans exactly the non-bottom targets. This identity also
holds for malformed inputs, before any topological precondition is imposed. -/
theorem coverRange_eq_backwardCoverAnyCheck (vista : Vista) :
    (vista.bottom+1==vista.nodes.size && coverRange vista.nodes.toList 0 (vista.nodes.size-1))=
      backwardCoverAnyCheck vista := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,beq_iff_eq,coverRange_iff,Nat.zero_add,Nat.zero_le,
    true_implies,noTableReference_false_iff,backwardCoverAnyCheck,List.all_eq_true,
    List.mem_range,Bool.or_eq_true,List.any_eq_true,referenceCheck_iff]
  constructor
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target inside
    by_cases same : target=vista.bottom
    · exact Or.inl same
    · exact Or.inr (covered target (by omega))
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target before
    rcases covered target (by omega) with same | reference
    · omega
    · exact reference

theorem coverRange_eq_closure_all (vista : Vista) (nodes : NodesValid vista)
    (bottomInside : vista.bottom < vista.nodes.size) :
    (vista.bottom+1==vista.nodes.size && coverRange vista.nodes.toList 0 (vista.nodes.size-1))=
      (closure vista).all id := by
  rw [coverRange_eq_backwardCoverAnyCheck]
  exact backwardCoverAnyCheck_eq_closure_all vista (nodesValid_topological vista nodes) bottomInside

end Counting.StackMachine.DagValidation
