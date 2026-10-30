import Counting.DagSemanticsValidityNodes
import Counting.DagSemanticsCanonical

namespace Counting.Executable

/-- The parent relation alone bounds every stored level by its topological
index. Full vista closure and absence of duplicate nodes are unnecessary. -/
theorem nodesValid_level_le_index (vista : Vista) (valid : NodesValid vista) (index : Nat)
    (inside : index<vista.nodes.size) : (vista.node index).level ≤ index := by
  induction index using Nat.strong_induction_on with
  | h index ih=>
    by_cases zero : (vista.node index).level=0
    · omega
    · obtain ⟨parent,_,before,level,_,_,_⟩:=nodeValid_positive vista index (valid index inside) zero
      have prior:=ih parent before (before.trans inside)
      omega

theorem maxLevelFold_le (nodes : List Node) (initial bound : Nat)
    (first : initial ≤ bound) (levels : ∀ node∈nodes,node.level ≤ bound) :
    nodes.foldl (fun n node=>max n node.level) initial ≤ bound := by
  induction nodes generalizing initial with
  | nil=>exact first
  | cons node rest ih=>
    apply ih (max initial node.level) (max_le first (levels node (by simp)))
    intro next member
    exact levels next (by simp [member])

/-- The executable canonicalizer's outer loop can be generated from the
explicit node count, even when level labels are encoded in binary. -/
theorem canonicalLevelCount_le_size (vista : Vista) (valid : NodesValid vista)
    (nonempty : 0<vista.nodes.size) :
    vista.nodes.foldl (fun n node=>max n node.level) 0+1 ≤ vista.nodes.size := by
  have bounded : ∀ node∈vista.nodes.toList,node.level ≤ vista.nodes.size-1 := by
    intro node member
    obtain ⟨index,inside,same⟩:=List.mem_iff_getElem.mp member
    have inArray : index<vista.nodes.size := by simpa using inside
    have level:=nodesValid_level_le_index vista valid index inArray
    have sameNode : vista.node index=node := by
      simpa [Vista.node,inArray] using same
    rw [sameNode] at level
    omega
  have maximum:=maxLevelFold_le vista.nodes.toList 0 (vista.nodes.size-1) (Nat.zero_le _) bounded
  simp only [Array.foldl_toList] at maximum
  omega

theorem canonicalLevelCount_le_size_of_valid (vista : Vista) (valid : vista.valid=true) :
    vista.nodes.foldl (fun n node=>max n node.level) 0+1 ≤ vista.nodes.size := by
  apply canonicalLevelCount_le_size vista (nodesValid_of_valid vista valid)
  simp only [Vista.valid,Bool.and_eq_true,decide_eq_true_eq] at valid
  omega

end Counting.Executable
