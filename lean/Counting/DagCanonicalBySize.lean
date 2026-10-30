import Counting.DagCanonicalBounds

namespace Counting.Executable

theorem levelNodes_above_max (source : Vista) (level : Nat)
    (above : source.nodes.foldl (fun n node=>max n node.level) 0 < level) :
    levelNodes source level=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro index member
  simp only [levelNodes,List.mem_filter,List.mem_range,beq_iff_eq] at member
  have bound := node_level_le_max source index member.1
  omega

theorem canonicalLevel_above_max (source : Vista) (state : CanonicalState) (level : Nat)
    (above : source.nodes.foldl (fun n node=>max n node.level) 0 < level) :
    canonicalLevel source state level=state := by
  simp [canonicalLevel,levelNodes_above_max source level above]

theorem canonicalState_padded (source : Vista) (count : Nat)
    (enough : source.nodes.foldl (fun n node=>max n node.level) 0+1 ≤ count) :
    (List.range count).foldl (canonicalLevel source) (#[],Array.replicate source.nodes.size 0)=canonicalState source := by
  let base := source.nodes.foldl (fun n node=>max n node.level) 0+1
  obtain ⟨extra,same⟩ := Nat.exists_eq_add_of_le enough
  rw [same]
  clear same enough count
  induction extra with
  | zero => simp [canonicalState]
  | succ extra ih =>
    rw [show base+(extra+1)=(base+extra)+1 by omega,List.range_succ,List.foldl_append,
      List.foldl_cons,List.foldl_nil,canonicalLevel_above_max]
    · exact ih
    · dsimp [base];omega

/-- A valid height-bounded DAG can be normalized by exactly one level pass
per explicit source node. Empty trailing levels leave the result unchanged. -/
theorem canonicalState_by_size (source : Vista) (valid : NodesValid source)
    (nonempty : 0 < source.nodes.size) :
    (List.range source.nodes.size).foldl (canonicalLevel source)
      (#[],Array.replicate source.nodes.size 0)=canonicalState source :=
  canonicalState_padded source source.nodes.size (canonicalLevelCount_le_size source valid nonempty)

end Counting.Executable
