import Counting.StackDagSelectedHeader
import Counting.StackDagParentBounds
import Counting.StackDagClean

namespace Counting.StackMachine.AuditAscend
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem nodeRead_outside (nodes : List Executable.Node) (index : Nat)
    (outside : nodes.length ≤ index) :
    (DagParser.nodeReadEffect index (Encoding.sequence Encoding.node nodes)).accepted=false := by
  have suffix (count : Nat) (values : List Executable.Node) :
      (manyEffect DagParser.node.effect count (Encoding.sequence Encoding.node values)).suffix=
        Encoding.sequence Encoding.node (values.drop count) := by
    induction count generalizing values with
    | zero => rfl
    | succ count ih =>
      cases values with
      | nil =>
        have bound:=DagParser.node.many_suffix_le (count+1) []
        exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero bound)
      | cons value values =>
        simp only [Encoding.sequence,manyEffect,productEffect,DagParser.node.roundtrip,List.drop_succ_cons]
        exact ih values
  have emptyRejected : (DagParser.node.effect []).accepted=false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    obtain ⟨node,suffix,impossible⟩:=(DagParser.node.accepts_iff []).mp accepted
    have lengths:=congrArg List.length impossible
    have positive : 0<(Encoding.node.encode node).length := by
      rw [Encoding.node_length];unfold Encoding.nodeBits;omega
    simp only [List.length_append,List.length_nil] at lengths
    omega
  simp only [DagParser.nodeReadEffect,readEffect,productEffect,skipEffect,suffix,
    List.drop_eq_nil_of_le outside,Encoding.sequence,emptyRejected,Bool.and_false]

def readMetadata : Routine 18 := sequence (DagValidation.headerRoutine 14 DagValidation.selectedHeaderRoles)
  (clearRegisters [0,1,3,19])

/-- Read one optional parent from the serialized table. The selected unary
index and complete table survive. Missing nodes return None. -/
def readParent : Routine 18 := sequence DagParser.preservingNodeRead
  (branchRoutine 1 readMetadata (clear 19))

theorem readMetadata_executes (store : Store 18) (node : Executable.Node)
    (source : store 19=Encoding.node.encode node)
    (empty : ∀ r : Fin 20,r∈([0,1,2,3,4] : List (Fin 20)) → store r=[]) :
    ∃ time ≤ 20*((Encoding.node.encode node).length+1),
      Executes readMetadata store time
        (Function.update (Function.update store 19 []) 2 (DagValidation.parentCode node).bits) := by
  obtain ⟨time,bound,a⟩:=DagValidation.header_executes 14 DagValidation.selectedHeaderRoles store
    (by simpa [DagValidation.selectedHeaderRoles] using empty 4 (by simp))
  let parsed:=DagValidation.headerStore 14 DagValidation.selectedHeaderRoles store
  have decoded : DagValidation.header (Encoding.node.encode node)=
      ⟨node.level.bits,(DagValidation.parentCode node).bits,[node.leader],DagValidation.nodeSuffix node,true⟩ := by
    simpa only [List.append_nil,DagValidation.nodeSuffix] using DagValidation.header_node node []
  have nodeLength : 1≤(Encoding.node.encode node).length := by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have metadataBound:=DagValidation.node_metadata_size_le node
  have suffixBound:=DagValidation.nodeSuffix_length_le node
  have size (r : Fin 20) (member : r∈([0,1,3,19] : List (Fin 20))) :
      (parsed r).length ≤ (Encoding.node.encode node).length := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    all_goals
      simp [parsed,DagValidation.headerStore,DagValidation.selectedHeaderRoles,
        source,decoded,empty,Encoding.bits_length]
      omega
  obtain ⟨clearTime,clearBound,b⟩:=DagValidation.clear_selected_executes [0,1,3,19] parsed _ size
  have final : clearedStore [0,1,3,19] parsed=
      Function.update (Function.update store 19 []) 2 (DagValidation.parentCode node).bits := by
    funext r
    fin_cases r <;> simp [clearedStore,parsed,DagValidation.headerStore,
      DagValidation.selectedHeaderRoles,source,decoded,empty]
  rw [final] at b
  change time ≤ 6*(store 19).length+17 at bound
  rw [source] at bound
  change clearTime ≤ 4*((Encoding.node.encode node).length+2) at clearBound
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditAscend

