import Counting.StackRealizabilityLevelFields
import Counting.StackDagClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def levelMetadata : List (Fin 27):=[0,3,19,24]
def levelItem : Routine 25:=sequence childHeader
  (sequence (ofProgram (unframeProgram 24 20 24 4))
    (sequence (clear 2) (sequence levelFieldsSum (sequence (clearRegisters levelMetadata) (pushBit 18 true)))))

def levelItemStore (store : Store 25) (node : Executable.Node) (target total value : Nat)
    (suffix : List Bool) : Store 25:=
  Function.update (Function.update (Function.update store 20 suffix)
    21 (total+levelContribution node target value).bits) 18 (true::store 18)

theorem levelItem_executes (store : Store 25) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 27,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e26 : store 26=[])
    (nodes : List Executable.Node) (index : Fin nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (counter : (store 18).length=index.val)
    (target total value : Nat) (level : store 22=target.bits) (e25 : store 25=[])
    (accumulator : store 21=total.bits)
    (suffix : List Bool) (input : store 20=Encoding.natural.encode value++suffix) :
    ∃ time ≤ 8000*((store 17).length+(store 20).length+total.size+target.size+1)^4,
      Executes levelItem store time (levelItemStore store nodes[index] target total value suffix):=by
  obtain ⟨headerTime,headerBound,headerRun⟩:=childHeader_executes store accepted tail status work e19
    nodes index nodeSuffix nodeInput counter
  let node:=nodes[index]
  let parsed:=childHeaderStore store node
  have parsing:=unframe_canonical_executes 24 20 24 4 (by decide) (by decide) (by decide)
    parsed value.bits suffix (by simp [parsed,childHeaderStore,input,Encoding.natural])
    (by simp [parsed,childHeaderStore,work])
  have outputEmpty : parsed 24=[]:=by simp [parsed,childHeaderStore,e24]
  rw [outputEmpty,List.append_nil] at parsing
  let ready:=Function.update (Function.update parsed 20 suffix) 24 value.bits
  have clearParent:=clear_executes (2:Fin 27) ready
  have parentValue : ready 2=(DagValidation.parentCode node).bits:=by simp [ready,parsed,childHeaderStore]
  rw [parentValue] at clearParent
  let prepared:=Function.update ready 2 []
  obtain ⟨sumTime,sumBound,sumRun⟩:=levelFieldsSum_executes prepared node target value total
    (by simp [prepared,ready,parsed,childHeaderStore]) (by simp [prepared])
    (by simp [prepared,ready,parsed,childHeaderStore,level]) (by simp [prepared,ready,parsed,childHeaderStore,e25])
    (by simp [prepared,ready]) (by simp [prepared,ready,parsed,childHeaderStore,accumulator])
    (by simp [prepared,ready,parsed,childHeaderStore,work]) (by simp [prepared,ready,parsed,childHeaderStore,work])
    (by simp [prepared,ready,parsed,childHeaderStore,work]) (by simp [prepared,ready,parsed,childHeaderStore,e26])
  let summed:=Function.update prepared 21 (total+levelContribution node target value).bits
  have metadata:=DagValidation.node_metadata_size_le node
  have suffixSize:=DagValidation.nodeSuffix_length_le node
  have codePositive : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have cleanupBound (r : Fin 27) (member : r∈levelMetadata) :
      (summed r).length ≤ (Encoding.node.encode node).length+value.size:=by
    simp only [levelMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change [node.leader].length ≤ _;simp only [List.length_cons,List.length_nil];omega
    · change (DagValidation.nodeSuffix node).length ≤ _;omega
    · change value.bits.length ≤ _;rw [Encoding.bits_length];omega
  obtain ⟨clearTime,clearBound,clearing⟩:=DagValidation.clear_selected_executes levelMetadata summed
    ((Encoding.node.encode node).length+value.size) cleanupBound
  let cleaned:=clearedStore levelMetadata summed
  have pushing:=pushBit_executes (18:Fin 27) true cleaned
  have indexValue : cleaned 18=store 18:=by
    simp [cleaned,clearedStore,levelMetadata,summed,prepared,ready,parsed,childHeaderStore]
  rw [indexValue] at pushing
  have final : Function.update cleaned 18 (true::store 18)=levelItemStore store node target total value suffix:=by
    funext r
    fin_cases r <;> simp [cleaned,clearedStore,levelMetadata,summed,prepared,ready,parsed,
      childHeaderStore,levelItemStore,work,e19,e24]
  rw [final] at pushing
  have entryLength:=DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeLength : (Encoding.node.encode node).length ≤ (store 17).length:=by rw [nodeInput,List.length_append];omega
  have valueLength : value.size ≤ (store 20).length:=by rw [input,List.length_append,Encoding.natural_length];omega
  let S:=(store 17).length+(store 20).length+total.size+target.size+1
  have headerLimit : headerTime ≤ 7000*S^4:=by
    apply headerBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4)
  have linear : S ≤ S^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change clearTime ≤ 4*((Encoding.node.encode node).length+value.size+2) at clearBound
  refine ⟨_,?_,headerRun.sequence (parsing.sequence (clearParent.sequence (sumRun.sequence (clearing.sequence pushing))))⟩
  simp only [Encoding.bits_length]
  change _ ≤ 8000*S^4
  dsimp only [S] at headerLimit linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
