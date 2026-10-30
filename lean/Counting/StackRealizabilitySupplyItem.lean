import Counting.StackRealizabilitySupplyFields
import Counting.StackRealizabilitySupplyHeader
import Counting.StackDagClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def supplyMetadata : List (Fin 30):=[0,2,3,19,24,27]
def supplyItem : Routine 28:=sequence supplyHeader
  (sequence (ofProgram (unframeProgram 27 20 24 4))
    (sequence (ofProgram (unframeProgram 27 19 27 4))
      (sequence supplyFieldsSum (sequence (clearRegisters supplyMetadata) (pushBit 18 true)))))

def supplyItemStore (store : Store 28) (node : Executable.Node) (target old total value : Nat)
    (suffix : List Bool) : Store 28:=
  Function.update (Function.update (Function.update store 20 suffix)
    26 (total+supplyContribution node target old value).bits) 18 (true::store 18)

theorem node_supply_fields_size (node : Executable.Node) :
    node.degree.size+node.level.size+(DagValidation.parentCode node).size ≤ (Encoding.node.encode node).length:=by
  rw [Encoding.node_length]
  unfold Encoding.nodeBits DagValidation.parentCode
  omega

theorem supplyItem_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (nodes : List Executable.Node) (index : Fin nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (counter : (store 18).length=index.val)
    (target old total value : Nat) (level : store 22=target.bits) (parent : store 25=(old+1).bits)
    (accumulator : store 26=total.bits)
    (suffix : List Bool) (input : store 20=Encoding.natural.encode value++suffix) :
    ∃ time ≤ 100000*((store 17).length+(store 20).length+total.size+target.size+(old+1).size+1)^4,
      Executes supplyItem store time (supplyItemStore store nodes[index] target old total value suffix):=by
  obtain ⟨headerTime,headerBound,headerRun⟩:=supplyHeader_executes store accepted tail status work e19
    nodes index nodeSuffix nodeInput counter
  let node:=nodes[index]
  let parsed:=supplyHeaderStore store node
  have parsing:=unframe_canonical_executes 27 20 24 4 (by decide) (by decide) (by decide)
    parsed value.bits suffix (by simp [parsed,supplyHeaderStore,input,Encoding.natural])
    (by simp [parsed,supplyHeaderStore,work])
  have outputEmpty : parsed 24=[]:=by simp [parsed,supplyHeaderStore,e24]
  rw [outputEmpty,List.append_nil] at parsing
  let ready:=Function.update (Function.update parsed 20 suffix) 24 value.bits
  let incoming:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming
  have parsingDegree:=unframe_canonical_executes 27 19 27 4 (by decide) (by decide) (by decide)
    ready node.degree.bits incoming
    (by simp [ready,parsed,supplyHeaderStore,DagValidation.nodeSuffix,incoming,Encoding.natural])
    (by simp [ready,parsed,supplyHeaderStore,work])
  have degreeEmpty : ready 27=[]:=by simp [ready,parsed,supplyHeaderStore,e27]
  rw [degreeEmpty,List.append_nil] at parsingDegree
  let withDegree:=Function.update (Function.update ready 19 incoming) 27 node.degree.bits
  have arithWork (r : Fin 30) (lower : 4 ≤ r.val) (upper : r.val<17) : withDegree r=[]:=by
    have n0 : r≠0:=by intro same;subst r;norm_num at lower
    have n1 : r≠1:=by intro same;subst r;norm_num at lower
    have n2 : r≠2:=by intro same;subst r;norm_num at lower
    have n3 : r≠3:=by intro same;subst r;norm_num at lower
    have n19 : r≠19:=by intro same;subst r;norm_num at upper
    have n20 : r≠20:=by intro same;subst r;norm_num at upper
    have n24 : r≠24:=by intro same;subst r;norm_num at upper
    have n27 : r≠27:=by intro same;subst r;norm_num at upper
    simp [withDegree,ready,parsed,supplyHeaderStore,n0,n2,n3,n19,n20,n24,n27,work r upper n1]
  obtain ⟨sumTime,sumBound,sumRun⟩:=supplyFieldsSum_executes withDegree node target old value total
    (by simp [withDegree,ready,parsed,supplyHeaderStore]) (by simp [withDegree,ready,parsed,supplyHeaderStore])
    (by simp [withDegree,ready,parsed,supplyHeaderStore,level]) (by simp [withDegree,ready,parsed,supplyHeaderStore,parent])
    (by simp [withDegree,ready]) (by simp [withDegree])
    (by simp [withDegree,ready,parsed,supplyHeaderStore,accumulator]) arithWork
    (by simp [withDegree,ready,parsed,supplyHeaderStore,e28]) (by simp [withDegree,ready,parsed,supplyHeaderStore,e29])
  let summed:=Function.update withDegree 26 (total+supplyContribution node target old value).bits
  have metadata:=node_supply_fields_size node
  have suffixSize:=DagValidation.nodeSuffix_length_le node
  have incomingSize : incoming.length ≤ (Encoding.node.encode node).length:=by
    change (Encoding.natural.encode node.degree++incoming).length ≤ _ at suffixSize
    simp only [List.length_append] at suffixSize
    omega
  have codePositive : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have cleanupBound (r : Fin 30) (member : r∈supplyMetadata) :
      (summed r).length ≤ (Encoding.node.encode node).length+value.size:=by
    simp only [supplyMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change (DagValidation.parentCode node).bits.length ≤ _;rw [Encoding.bits_length];omega
    · change [node.leader].length ≤ _;simp only [List.length_cons,List.length_nil];omega
    · change incoming.length ≤ _;omega
    · change value.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change node.degree.bits.length ≤ _;rw [Encoding.bits_length];omega
  obtain ⟨clearTime,clearBound,clearing⟩:=DagValidation.clear_selected_executes supplyMetadata summed
    ((Encoding.node.encode node).length+value.size) cleanupBound
  let cleaned:=clearedStore supplyMetadata summed
  have pushing:=pushBit_executes (18:Fin 30) true cleaned
  have indexValue : cleaned 18=store 18:=by
    simp [cleaned,clearedStore,supplyMetadata,summed,withDegree,ready,parsed,supplyHeaderStore]
  rw [indexValue] at pushing
  have final : Function.update cleaned 18 (true::store 18)=supplyItemStore store node target old total value suffix:=by
    funext r
    fin_cases r <;> simp [cleaned,clearedStore,supplyMetadata,summed,withDegree,ready,parsed,
      supplyHeaderStore,supplyItemStore,work,e19,e24,e27]
  rw [final] at pushing
  have entryLength:=DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeLength : (Encoding.node.encode node).length ≤ (store 17).length:=by rw [nodeInput,List.length_append];omega
  have valueLength : value.size ≤ (store 20).length:=by rw [input,List.length_append,Encoding.natural_length];omega
  let S:=(store 17).length+(store 20).length+total.size+target.size+(old+1).size+1
  have headerLimit : headerTime ≤ 7000*S^4:=by
    apply headerBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4)
  have sumLimit : sumTime ≤ 84000*S^3:=by
    apply sumBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have cube : S^3 ≤ S^4:=Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4:=Nat.one_le_pow _ _ positive
  change clearTime ≤ 6*((Encoding.node.encode node).length+value.size+2) at clearBound
  refine ⟨_,?_,headerRun.sequence (parsing.sequence (parsingDegree.sequence (sumRun.sequence (clearing.sequence pushing))))⟩
  simp only [Encoding.bits_length]
  change _ ≤ 100000*S^4
  dsimp only [S] at headerLimit sumLimit cube linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
