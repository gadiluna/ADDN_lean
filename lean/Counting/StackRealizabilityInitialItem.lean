import Counting.StackRealizabilityInitialHeader
import Counting.StackRealizabilityInitialAccumulate
import Counting.StackDagClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def initialMetadata : List (Fin 26):=[0,2,3,19]

def initialItem : Routine 24:=sequence initialHeader
  (sequence (ofProgram (unframeProgram 23 20 24 4))
    (sequence initialSum (sequence (clearRegisters initialMetadata) (pushBit 18 true))))

def initialContribution (node : Executable.Node) (leader : Bool) (value : Nat) : Nat:=
  if node.level=0 ∧ node.leader=leader then value else 0

def initialItemStore (store : Store 24) (node : Executable.Node) (leaders nonleaders value : Nat)
    (suffix : List Bool) : Store 24:=
  Function.update (Function.update (Function.update (Function.update store 20 suffix)
    21 (leaders+initialContribution node true value).bits)
    22 (nonleaders+initialContribution node false value).bits) 18 (true::store 18)

theorem initialItem_executes (store : Store 24) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 26,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (nodes : List Executable.Node) (index : Fin nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (counter : (store 18).length=index.val)
    (leaders nonleaders value : Nat) (first : store 21=leaders.bits) (second : store 22=nonleaders.bits)
    (suffix : List Bool) (input : store 20=Encoding.natural.encode value++suffix) :
    ∃ time ≤ 8000*((store 17).length+(store 20).length+leaders.size+nonleaders.size+1)^4,
      Executes initialItem store time (initialItemStore store nodes[index] leaders nonleaders value suffix):=by
  obtain ⟨headerTime,headerBound,headerRun⟩:=initialHeader_executes store accepted tail status work e19
    nodes index nodeSuffix nodeInput counter
  let node:=nodes[index]
  let parsed:=initialHeaderStore store node
  have parsing:=unframe_canonical_executes 23 20 24 4 (by decide) (by decide) (by decide)
    parsed value.bits suffix (by simp [parsed,initialHeaderStore,input,Encoding.natural])
    (by simp [parsed,initialHeaderStore,work])
  have outputEmpty : parsed 24=[]:=by simp [parsed,initialHeaderStore,e24]
  rw [outputEmpty,List.append_nil] at parsing
  let ready:=Function.update (Function.update parsed 20 suffix) 24 value.bits
  obtain ⟨sumTime,sumBound,sumRun⟩:=initialSum_executes ready node.level node.leader leaders nonleaders value
    (by simp [ready,parsed,initialHeaderStore]) (by simp [ready,parsed,initialHeaderStore])
    (by simp [ready,parsed,initialHeaderStore,first]) (by simp [ready,parsed,initialHeaderStore,second])
    (by simp [ready]) (by simp [ready,parsed,initialHeaderStore,work])
    (by simp [ready,parsed,initialHeaderStore,work]) (by simp [ready,parsed,initialHeaderStore,e25])
  let summed:=initialSumStore ready node.level node.leader leaders nonleaders value
  have metadata:=DagValidation.node_metadata_size_le node
  have suffixSize:=DagValidation.nodeSuffix_length_le node
  have codePositive : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have cleanupBound (r : Fin 26) (member : r∈initialMetadata) :
      (summed r).length≤(Encoding.node.encode node).length:=by
    simp only [initialMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · change node.level.bits.length≤_;rw [Encoding.bits_length];omega
    · change (DagValidation.parentCode node).bits.length≤_;rw [Encoding.bits_length];omega
    · change (if node.level=0 then [] else [node.leader]).length≤_
      split_ifs <;> simp only [List.length_nil,List.length_cons] <;> omega
    · exact suffixSize
  obtain ⟨clearTime,clearBound,clearing⟩:=DagValidation.clear_selected_executes initialMetadata summed
    (Encoding.node.encode node).length cleanupBound
  let cleaned:=clearedStore initialMetadata summed
  have pushing:=pushBit_executes (18:Fin 26) true cleaned
  have indexValue : cleaned 18=store 18:=by
    simp [cleaned,clearedStore,initialMetadata,summed,initialSumStore,ready,parsed,initialHeaderStore]
  rw [indexValue] at pushing
  have final : Function.update cleaned 18 (true::store 18)=initialItemStore store node leaders nonleaders value suffix:=by
    funext r
    fin_cases r <;> simp [cleaned,clearedStore,initialMetadata,summed,initialSumStore,ready,parsed,
      initialHeaderStore,initialItemStore,initialContribution,work,e19,e24]
  rw [final] at pushing
  have entryLength:=DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeLength : (Encoding.node.encode node).length≤(store 17).length:=by rw [nodeInput,List.length_append];omega
  have valueLength : value.size≤(store 20).length:=by rw [input,List.length_append,Encoding.natural_length];omega
  let S:=(store 17).length+(store 20).length+leaders.size+nonleaders.size+1
  have headerLimit : headerTime≤7000*S^4:=by apply headerBound.trans;gcongr;dsimp only [S];omega
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change clearTime≤4*((Encoding.node.encode node).length+2) at clearBound
  refine ⟨_,?_,headerRun.sequence (parsing.sequence (sumRun.sequence (clearing.sequence pushing)))⟩
  rw [Encoding.bits_length]
  change _≤8000*S^4
  dsimp only [S] at headerLimit linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
