import Counting.StackRealizabilityDemandEdgePrefix
import Counting.StackRealizabilityDemandHeader
import Counting.StackFrameSkip
import Counting.StackDagClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def demandMetadata : List (Fin 32):=[0,3,24]
def demandItem : Routine 30:=sequence demandHeader
  (sequence (ofProgram (unframeProgram 29 20 24 4))
    (sequence (ofProgram (FieldAccess.skipProgram 30 19))
      (sequence (clear 2) (sequence demandEdgePrefix
        (sequence (clearRegisters demandMetadata) (pushBit 18 true))))))

def demandItemStore (store : Store 30) (node : Executable.Node) (target old total value : Nat)
    (suffix : List Bool) : Store 30:=
  Function.update (Function.update (Function.update store 20 suffix)
    26 (total+demandEdges node.level target old value node.incoming).bits) 18 (true::store 18)

theorem node_demand_fields_size (node : Executable.Node) :
    ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).length+
      node.level.size+(DagValidation.parentCode node).size ≤ (Encoding.node.encode node).length:=by
  rw [Encoding.node_length,Encoding.list_length]
  simp only [Encoding.product,List.length_append,Encoding.natural_length]
  unfold Encoding.nodeBits DagValidation.parentCode
  omega

theorem demandItem_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e30 : store 30=[]) (e31 : store 31=[])
    (nodes : List Executable.Node) (index : Fin nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (counter : (store 18).length=index.val)
    (target old total value : Nat) (level : store 22=target.bits) (source : store 25=old.bits)
    (accumulator : store 26=total.bits)
    (suffix : List Bool) (input : store 20=Encoding.natural.encode value++suffix) :
    ∃ time ≤ 720000*((store 17).length+(store 20).length+total.size+target.size+old.size+1)^7,
      Executes demandItem store time (demandItemStore store nodes[index] target old total value suffix):=by
  obtain ⟨headerTime,headerBound,headerRun⟩:=demandHeader_executes store accepted tail status work e19
    nodes index nodeSuffix nodeInput counter
  let node:=nodes[index]
  let parsed:=demandHeaderStore store node
  have parsing:=unframe_canonical_executes 29 20 24 4 (by decide) (by decide) (by decide)
    parsed value.bits suffix (by simp [parsed,demandHeaderStore,input,Encoding.natural])
    (by simp [parsed,demandHeaderStore,work])
  have outputEmpty : parsed 24=[]:=by simp [parsed,demandHeaderStore,e24]
  rw [outputEmpty,List.append_nil] at parsing
  let ready:=Function.update (Function.update parsed 20 suffix) 24 value.bits
  let incoming:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming
  have skipping:=FieldAccess.skip_executes 30 19 ready
  have skipInput : ready 19=Encoding.frame node.degree.bits++incoming:=by
    simp [ready,parsed,demandHeaderStore,DagValidation.nodeSuffix,incoming,Encoding.natural]
  rw [skipInput,FieldAccess.skipRest_frame,FieldAccess.skipCost_frame] at skipping
  let skipped:=Function.update ready 19 incoming
  have clearingParent:=clear_executes (2:Fin 32) skipped
  have parentValue : skipped 2=(DagValidation.parentCode node).bits:=by
    simp [skipped,ready,parsed,demandHeaderStore]
  rw [parentValue] at clearingParent
  let prepared:=Function.update skipped 2 []
  have preparedWork (r : Fin 32) (lo : 4 ≤ r.val) (hi : r.val<17) : prepared r=[]:=by
    have n0 : r≠0:=by intro same;subst r;norm_num at lo
    have n1 : r≠1:=by intro same;subst r;norm_num at lo
    have n2 : r≠2:=by intro same;subst r;norm_num at lo
    have n3 : r≠3:=by intro same;subst r;norm_num at lo
    have n19 : r≠19:=by intro same;subst r;norm_num at hi
    have n20 : r≠20:=by intro same;subst r;norm_num at hi
    have n24 : r≠24:=by intro same;subst r;norm_num at hi
    simp [prepared,skipped,ready,parsed,demandHeaderStore,n0,n2,n3,n19,n20,n24,work r hi n1]
  obtain ⟨edgeTime,edgeBound,edgeRun⟩:=demandEdgePrefix_executes prepared accepted tail
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,status]) node.level target old value total
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,level])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,source])
    (by simp [prepared,skipped,ready])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,accumulator]) preparedWork
    (by simp [prepared]) (by simp [prepared,skipped,ready,parsed,demandHeaderStore,e27])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,e28])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,e29])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,e30])
    (by simp [prepared,skipped,ready,parsed,demandHeaderStore,e31]) node.incoming []
    (by simp [prepared,skipped,incoming])
  let summed:=demandEdgePrefixStore prepared node.level target old value total node.incoming []
  have metadata:=node_demand_fields_size node
  have degreeSize:=DagValidation.nodeSuffix_length_le node
  have degreeBound : node.degree.size ≤ (Encoding.node.encode node).length:=by
    change (Encoding.natural.encode node.degree++incoming).length ≤ _ at degreeSize
    simp only [List.length_append,Encoding.natural_length] at degreeSize
    omega
  have codePositive : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have cleanupBound (r : Fin 32) (member : r∈demandMetadata) :
      (summed r).length ≤ (Encoding.node.encode node).length+value.size:=by
    simp only [demandMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change [node.leader].length ≤ _;simp only [List.length_cons,List.length_nil];omega
    · change value.bits.length ≤ _;rw [Encoding.bits_length];omega
  obtain ⟨clearTime,clearBound,clearing⟩:=DagValidation.clear_selected_executes demandMetadata summed
    ((Encoding.node.encode node).length+value.size) cleanupBound
  let cleaned:=clearedStore demandMetadata summed
  have pushing:=pushBit_executes (18:Fin 32) true cleaned
  have indexValue : cleaned 18=store 18:=by
    simp [cleaned,clearedStore,demandMetadata,summed,demandEdgePrefixStore,prepared,skipped,ready,parsed,demandHeaderStore]
  rw [indexValue] at pushing
  have final : Function.update cleaned 18 (true::store 18)=demandItemStore store node target old total value suffix:=by
    funext r
    fin_cases r <;> simp [cleaned,clearedStore,demandMetadata,summed,demandEdgePrefixStore,prepared,skipped,
      ready,parsed,demandHeaderStore,demandItemStore,work,e19,e24]
  rw [final] at pushing
  have entryLength:=DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeLength : (Encoding.node.encode node).length ≤ (store 17).length:=by rw [nodeInput,List.length_append];omega
  have valueLength : value.size ≤ (store 20).length:=by rw [input,List.length_append,Encoding.natural_length];omega
  let S:=(store 17).length+(store 20).length+total.size+target.size+old.size+1
  have headerLimit : headerTime ≤ 7000*S^4:=by
    apply headerBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4)
  have edgeLimit : edgeTime ≤ 700000*S^7:=by
    apply edgeBound.trans
    apply Nat.mul_le_mul_left _
    apply Nat.pow_le_pow_left
    change incoming.length+node.level.size+target.size+old.size+value.size+total.size+1 ≤ S
    dsimp only [S,incoming];omega
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have fourth : S^4 ≤ S^7:=Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^7:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^7:=Nat.one_le_pow _ _ positive
  change clearTime ≤ 3*((Encoding.node.encode node).length+value.size+2) at clearBound
  refine ⟨_,?_,headerRun.sequence (parsing.sequence (skipping.sequence
    (clearingParent.sequence (edgeRun.sequence (clearing.sequence pushing)))))⟩
  simp only [Encoding.bits_length]
  change _ ≤ 720000*S^7
  dsimp only [S] at headerLimit edgeLimit fourth linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
