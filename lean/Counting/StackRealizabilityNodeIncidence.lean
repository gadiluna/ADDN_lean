import Counting.StackAnchorCoefficientSelect
import Counting.StackRealizabilityIncoming

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def incidenceMetadata : List (Fin 34):=[23,24,25,26,27,28]

/-- Read an actual serialized node and calculate its parent incidence and
first-match incoming incidence. The sender identifier is only a DAG index;
the predecessor-plus-one payload is computed by the machine. -/
def nodeIncidence : Routine 32:=sequence AnchorCoefficient.readNode
  (sequence AnchorCoefficient.findCount
    (sequence AnchorCoefficient.prepareQuery
      (sequence (Compare.preservingEquality 28 AnchorCoefficient.equalityRoles)
        (sequence (positiveBitsFlag 27 22) (clearRegisters incidenceMetadata)))))

theorem nodeIncidence_executes (node : Executable.Node) (query : Nat) (suffix result : List Bool) :
    ∃ time ≤ 8000*((Encoding.node.encode node).length+suffix.length+query.size+1)^3,
      Executes nodeIncidence
        (AnchorCoefficient.file (Encoding.node.encode node++suffix) query.bits result [] [] [] [] [] [] []) time
        (AnchorCoefficient.file suffix query.bits (decide (0<Executable.countFrom node query)::result)
          [] [] [] [] [] [] [decide (node.parent=some query)]):=by
  obtain ⟨readTime,readBound,reading⟩:=AnchorCoefficient.readNode_executes node query suffix result
  obtain ⟨findTime,findBound,finding⟩:=AnchorCoefficient.findCount_executes node query suffix result
  let found:=AnchorCoefficient.file suffix query.bits result node.level.bits
    (DagValidation.parentCode node).bits [node.leader] node.degree.bits
    (Executable.countFrom node query).bits [] []
  obtain ⟨prepareTime,prepareBound,preparing⟩:=AnchorCoefficient.prepareQuery_executes found query
    (by simp [found,AnchorCoefficient.file]) (by simp [found,AnchorCoefficient.file])
    (by simp [found,AnchorCoefficient.file]) (by simp [found,AnchorCoefficient.file])
  let prepared:=Function.update found 28 (query+1).bits
  have comparing:=Compare.preservingEquality_executes 28 AnchorCoefficient.equalityRoles prepared
    (by simp [prepared,found,AnchorCoefficient.file,AnchorCoefficient.equalityRoles])
    (by simp [prepared,found,AnchorCoefficient.file,AnchorCoefficient.equalityRoles])
    (by simp [prepared,found,AnchorCoefficient.file,AnchorCoefficient.equalityRoles])
  change Executes (Compare.preservingEquality 28 AnchorCoefficient.equalityRoles) prepared
    (Compare.preservingCost (prepared 24) (prepared 28))
    (Function.update prepared 32 (decide (prepared 24=prepared 28)::prepared 32)) at comparing
  have parentAt : prepared 24=(DagValidation.parentCode node).bits:=by simp [prepared,found,AnchorCoefficient.file]
  have successorAt : prepared 28=(query+1).bits:=by simp [prepared]
  have flagAt : prepared 32=[]:=by simp [prepared,found,AnchorCoefficient.file]
  rw [parentAt,successorAt,flagAt] at comparing
  simp only [Encoding.bits_injective.eq_iff,AnchorCoefficient.parentCode_eq] at comparing
  let compared:=Function.update prepared 32 [decide (node.parent=some query)]
  obtain ⟨positiveTime,positiveBound,positiveRun⟩:=positiveBitsFlag_executes (27:Fin 34) 22 compared
    (Executable.countFrom node query) (by simp [compared,prepared,found,AnchorCoefficient.file])
  have resultAt : compared 22=result:=by simp [compared,prepared,found,AnchorCoefficient.file]
  rw [resultAt] at positiveRun
  let tested:=Function.update compared 22 (decide (0<Executable.countFrom node query)::result)
  have parentBound:=DagValidation.node_metadata_size_le node
  have degreeBound : node.degree.size≤(Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have countBound : (Executable.countFrom node query).size≤(Encoding.node.encode node).length:=by
    simpa only [Encoding.node_length] using Encoding.redBits_le_node node query
  have successorBound : (query+1).size≤query.size+1:=by
    have bound:=DagValidation.increment_length_le query.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using bound
  have cleanupLimit (r : Fin 34) (member : r∈incidenceMetadata) :
      (tested r).length≤(Encoding.node.encode node).length+query.size+1:=by
    simp only [incidenceMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [tested,compared,prepared,found,AnchorCoefficient.file,Encoding.bits_length]
    all_goals omega
  obtain ⟨cleanupTime,cleanupBound,cleanup⟩:=DagValidation.clear_selected_executes incidenceMetadata tested
    ((Encoding.node.encode node).length+query.size+1) cleanupLimit
  have final : clearedStore incidenceMetadata tested=
      AnchorCoefficient.file suffix query.bits (decide (0<Executable.countFrom node query)::result)
        [] [] [] [] [] [] [decide (node.parent=some query)]:=by
    funext r
    fin_cases r <;> simp [clearedStore,incidenceMetadata,tested,compared,prepared,found,AnchorCoefficient.file]
  rw [final] at cleanup
  have equalityBound:=Compare.preservingCost_le (DagValidation.parentCode node).bits (query+1).bits
  simp only [Encoding.bits_length] at equalityBound
  have incomingBound : ((Encoding.list AnchorFind.edgeCodec).encode node.incoming).length≤
      (Encoding.node.encode node).length:=by
    have bound:=DagValidation.nodeSuffix_length_le node
    unfold DagValidation.nodeSuffix at bound
    simp only [List.length_append] at bound
    exact le_trans (Nat.le_add_left _ _) bound
  let S:=(Encoding.node.encode node).length+suffix.length+query.size+1
  have findLimit : findTime≤5000*S^3:=by
    apply findBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simp only [List.length_append];dsimp only [S];omega) 3)
  have linear : S≤S^3:=Nat.le_self_pow (by decide) _
  have one : 1≤S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change cleanupTime≤6*((Encoding.node.encode node).length+query.size+1+2) at cleanupBound
  simp only [List.length_append] at readBound
  have execution:=reading.sequence (finding.sequence (preparing.sequence (comparing.sequence (positiveRun.sequence cleanup))))
  exact ⟨_,by change _≤8000*S^3;dsimp only [S] at findLimit linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
