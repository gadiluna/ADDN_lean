import Counting.StackDagCoverPrefix
import Counting.StackDagDistinctSpec

namespace Counting.StackMachine.DagValidation

/-- The three predicates realized by the three concrete table scans. -/
def semanticCheck (vista : Executable.Vista) : Bool:=
  nodeRangeCheck vista.nodes.toList 0 vista.nodes.size &&
    distinctAllRange vista.nodes.toList 0 vista.nodes.size && coverCheck vista.nodes.toList vista.bottom

theorem semanticCheck_eq_valid (vista : Executable.Vista) : semanticCheck vista=vista.valid:=by
  apply Bool.eq_iff_iff.mpr
  simp only [semanticCheck,Bool.and_eq_true,nodeRangeCheck_vista,distinctAllRange_eraseDups]
  constructor
  · rintro ⟨⟨nodes,distinct⟩,cover⟩
    have nodeValid : Executable.NodesValid vista:=by
      simpa only [Executable.NodesValid,List.all_eq_true,List.mem_range] using nodes
    have last : vista.bottom+1=vista.nodes.size:=by
      have both : vista.bottom+1=vista.nodes.toList.length ∧ coverRange vista.nodes.toList 0 (vista.nodes.toList.length-1)=true:=by
        simpa only [coverCheck,Bool.and_eq_true,beq_iff_eq] using cover
      simpa only [Array.length_toList] using both.1
    have inside : vista.bottom<vista.nodes.size:=by omega
    have closed : (Executable.closure vista).all id=true:=by
      rw [←coverCheck_eq_closure vista nodeValid inside]
      exact cover
    simp only [Executable.Vista.valid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨⟨⟨inside,nodes⟩,distinct⟩,closed⟩
  · intro valid
    have parts : vista.bottom<vista.nodes.size ∧
        (List.range vista.nodes.size).all (Executable.nodeValid vista)=true ∧
        vista.nodes.toList.eraseDups.length=vista.nodes.size ∧ (Executable.closure vista).all id=true:=by
      simpa only [Executable.Vista.valid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] using valid
    have nodeValid : Executable.NodesValid vista:=by
      simpa only [Executable.NodesValid,List.all_eq_true,List.mem_range] using parts.2.1
    exact ⟨⟨parts.2.1,parts.2.2.1⟩,by rw [coverCheck_eq_closure vista nodeValid parts.1];exact parts.2.2.2⟩

end Counting.StackMachine.DagValidation
