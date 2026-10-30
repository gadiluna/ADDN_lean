import Counting.StackRealizabilitySupplyHeader
import Counting.StackComparePreserving
import Counting.StackDagClean

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def headerRoles : Fin 30 ↪ Fin 32 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 32=>r.val) equal)⟩
def compareRoles : Fin 6 ↪ Fin 32 := ⟨![0,30,31,4,5,6],by decide⟩
def metadata : List (Fin 32) := [0,2,3,19]

def headerStore (store : Store 30) (node : Executable.Node) : Store 30 :=
  fun r=>if r=0 then node.level.bits else if r=2 then (DagValidation.parentCode node).bits
    else if r=3 then [node.leader] else if r=19 then DagValidation.nodeSuffix node else store r

/-- Select the level of the actual indexed DAG node. The table and unary
index are preserved; metadata is explicitly erased after comparison. -/
abbrev selectedLevel : Routine 30 := sequence (relocate RealizabilityCheck.supplyHeader headerRoles)
  (sequence (Compare.preservingEquality 26 compareRoles) (clearRegisters metadata))

theorem selectedLevel_executes (store : Store 30) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 32,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (nodes : List Executable.Node) (index : Fin nodes.length)
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val) (target : Nat) (query : store 30=target.bits) :
    ∃ time ≤ 8000*((store 17).length+target.size+1)^4,
      Executes selectedLevel store time
        (Function.update store 31 (decide (nodes[index].level=target)::store 31)) := by
  let localStore : Store 28 := store ∘ headerRoles
  have localWork (r : Fin 30) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    apply work (headerRoles r) small
    intro equal
    apply different
    exact Fin.ext (congrArg (fun i:Fin 32=>i.val) equal)
  obtain ⟨headerTime,headerBound,read⟩ := RealizabilityCheck.supplyHeader_executes localStore accepted tail status
    localWork e19 nodes index suffix input counter
  let node := nodes[index]
  let parsed := headerStore store node
  have a : Executes (relocate RealizabilityCheck.supplyHeader headerRoles) store headerTime parsed := by
    apply relocate_executes_frame RealizabilityCheck.supplyHeader headerRoles _ _ _ _ headerTime rfl _ _ read
    · intro r;fin_cases r <;> simp [parsed,headerStore,RealizabilityCheck.supplyHeaderStore,localStore,headerRoles,node]
    · intro r outside
      have n0 : r≠0 := by intro eq;subst r;exact outside 0 rfl
      have n2 : r≠2 := by intro eq;subst r;exact outside 2 rfl
      have n3 : r≠3 := by intro eq;subst r;exact outside 3 rfl
      have n19 : r≠19 := by intro eq;subst r;exact outside 19 rfl
      simp [parsed,headerStore,n0,n2,n3,n19]
  have b := Compare.preservingEquality_executes 26 compareRoles parsed
    (by simp [compareRoles,parsed,headerStore,work]) (by simp [compareRoles,parsed,headerStore,work])
    (by simp [compareRoles,parsed,headerStore,work])
  have left : parsed (compareRoles 0)=node.level.bits := rfl
  have right : parsed (compareRoles 1)=target.bits := by simp [parsed,headerStore,compareRoles,query]
  have flag : parsed (compareRoles 2)=store 31 := rfl
  rw [left,right,flag] at b
  have bitsEqual : node.level.bits=target.bits ↔ node.level=target := Encoding.bits_injective.eq_iff
  simp only [bitsEqual] at b
  let compared := Function.update parsed 31 (decide (node.level=target)::store 31)
  have bRun : Executes (Compare.preservingEquality 26 compareRoles) parsed
      (Compare.preservingCost node.level.bits target.bits) compared := b
  have nodeLength := DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeBound : (Encoding.node.encode node).length ≤ (store 17).length := by
    rw [input,List.length_append];omega
  have metadataSize := DagValidation.node_metadata_size_le node
  have tailBound := DagValidation.nodeSuffix_length_le node
  have positive : 0<(Encoding.node.encode node).length := by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  have clearBound (r : Fin 32) (member : r∈metadata) : (compared r).length ≤ (Encoding.node.encode node).length := by
    simp only [metadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change (DagValidation.parentCode node).bits.length ≤ _;rw [Encoding.bits_length];omega
    · change 1 ≤ _;omega
    · change (DagValidation.nodeSuffix node).length ≤ _;exact tailBound
  obtain ⟨clearTime,clearLimit,c⟩ := DagValidation.clear_selected_executes metadata compared
    (Encoding.node.encode node).length clearBound
  have result : clearedStore metadata compared=Function.update store 31 (decide (node.level=target)::store 31) := by
    funext r;fin_cases r <;> simp [clearedStore,metadata,compared,parsed,headerStore,work,e19]
  rw [result] at c
  refine ⟨_,?_,a.sequence (bRun.sequence c)⟩
  have comparison := Compare.preservingCost_le node.level.bits target.bits
  simp only [Encoding.bits_length] at comparison
  let size := (store 17).length+target.size+1
  have raised : ((store 17).length+1)^4 ≤ size^4 := Nat.pow_le_pow_left (by dsimp only [size];omega) 4
  have linear : size ≤ size^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^4 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  have sourceSize : (store 17).length ≤ size := by dsimp only [size];omega
  have targetSize : target.size ≤ size := by dsimp only [size];omega
  change headerTime ≤ 7000*((store 17).length+1)^4 at headerBound
  change clearTime ≤ 4*((Encoding.node.encode node).length+2) at clearLimit
  change _ ≤ 8000*size^4
  omega

end Counting.StackMachine.AuditPropagation
