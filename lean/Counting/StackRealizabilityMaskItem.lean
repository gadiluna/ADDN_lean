import Counting.StackRealizabilityMaskFields
import Counting.StackDagClean
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def maskMetadata : List (Fin 30):=[0,2,3,19,27]
def maskItem : Routine 28:=sequence supplyHeader
  (sequence (ofProgram (unframeProgram 27 19 27 4))
    (sequence maskFields (sequence (clearRegisters maskMetadata) (pushBit 18 true))))

def maskItemStore (store : Store 28) (node : Executable.Node) (old next : Nat) : Store 28:=
  Function.update (maskFieldsStore store node old next) 18 (true::store 18)

theorem maskItem_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e27 : store 27=[])
    (nodes : List Executable.Node) (index : Fin nodes.length)
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val)
    (old next : Nat) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits) :
    ∃ time ≤ 8000*((store 17).length+old.size+next.size+1)^4,
      Executes maskItem store time (maskItemStore store nodes[index] old next):=by
  obtain ⟨headerTime,headerBound,headerRun⟩:=supplyHeader_executes store accepted tail status work e19
    nodes index suffix input counter
  let node:=nodes[index]
  let parsed:=supplyHeaderStore store node
  let incoming:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming
  have parsing:=unframe_canonical_executes 27 19 27 4 (by decide) (by decide) (by decide)
    parsed node.degree.bits incoming
    (by simp [parsed,supplyHeaderStore,DagValidation.nodeSuffix,incoming,Encoding.natural])
    (by simp [parsed,supplyHeaderStore,work])
  have degreeEmpty : parsed 27=[]:=by simp [parsed,supplyHeaderStore,e27]
  rw [degreeEmpty,List.append_nil] at parsing
  let withDegree:=Function.update (Function.update parsed 19 incoming) 27 node.degree.bits
  obtain ⟨fieldTime,fieldBound,fieldRun⟩:=maskFields_executes withDegree node old next
    (by simp [withDegree,parsed,supplyHeaderStore])
    (by simp [withDegree,parsed,supplyHeaderStore,oldAt])
    (by simp [withDegree,parsed,supplyHeaderStore,nextAt])
    (by simp [withDegree])
    (by simp [withDegree,parsed,supplyHeaderStore,work])
    (by simp [withDegree,parsed,supplyHeaderStore,work])
    (by simp [withDegree,parsed,supplyHeaderStore,work])
  let masked:=maskFieldsStore withDegree node old next
  have metadata:=DagValidation.node_metadata_size_le node
  have degreeSize : node.degree.size ≤ (Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have suffixSize:=DagValidation.nodeSuffix_length_le node
  have incomingSize : incoming.length ≤ (Encoding.node.encode node).length:=by
    change (Encoding.natural.encode node.degree++incoming).length ≤ _ at suffixSize
    simp only [List.length_append] at suffixSize
    omega
  have positive : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have cleanupBound (r : Fin 30) (member : r∈maskMetadata) :
      (masked r).length ≤ (Encoding.node.encode node).length:=by
    simp only [maskMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change (DagValidation.parentCode node).bits.length ≤ _;rw [Encoding.bits_length];omega
    · change 1 ≤ _;omega
    · change incoming.length ≤ _;exact incomingSize
    · change node.degree.bits.length ≤ _;rw [Encoding.bits_length];exact degreeSize
  obtain ⟨clearTime,clearBound,clearing⟩:=DagValidation.clear_selected_executes maskMetadata masked
    (Encoding.node.encode node).length cleanupBound
  let cleaned:=clearedStore maskMetadata masked
  have pushing:=pushBit_executes (18:Fin 30) true cleaned
  have indexAt : cleaned 18=store 18:=by
    simp [cleaned,clearedStore,maskMetadata,masked,maskFieldsStore,withDegree,parsed,supplyHeaderStore]
  rw [indexAt] at pushing
  have final : Function.update cleaned 18 (true::store 18)=maskItemStore store node old next:=by
    funext r
    fin_cases r <;> simp [cleaned,clearedStore,maskMetadata,masked,maskFieldsStore,withDegree,parsed,
      supplyHeaderStore,maskItemStore,work,e19,e27]
  rw [final] at pushing
  have entry:=DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeLength : (Encoding.node.encode node).length ≤ (store 17).length:=by
    rw [input,List.length_append]
    omega
  let S:=(store 17).length+old.size+next.size+1
  have headerLimit : headerTime ≤ 7000*S^4:=by
    apply headerBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4)
  have fieldLimit : fieldTime ≤ 40*S:=by
    apply fieldBound.trans
    dsimp only [S]
    omega
  have linear : S ≤ S^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change clearTime ≤ 5*((Encoding.node.encode node).length+2) at clearBound
  refine ⟨_,?_,headerRun.sequence (parsing.sequence (fieldRun.sequence (clearing.sequence pushing)))⟩
  simp only [Encoding.bits_length]
  change _ ≤ 8000*S^4
  dsimp only [S] at headerLimit fieldLimit linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
