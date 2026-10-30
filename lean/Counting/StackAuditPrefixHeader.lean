import Counting.StackAuditPropagationSelect
import Counting.StackRoutineMove

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def headerRoles : Fin 30 ↪ Fin 36 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 36=>r.val) equal)⟩
def levelRoles : Fin 6 ↪ Fin 36 := ⟨![0,30,31,4,5,6],by decide⟩
def parentRoles : Fin 6 ↪ Fin 36 := ⟨![2,32,33,4,5,6],by decide⟩
def headerMetadata : List (Fin 36) := [0,2,19]

def parsedHeader (store : Store 34) (node : Executable.Node) : Store 34 :=
  fun r=>if r=0 then node.level.bits else if r=2 then (DagValidation.parentCode node).bits
    else if r=3 then [node.leader] else if r=19 then DagValidation.nodeSuffix node else store r

/-- Read the actual indexed node once, compare both binary labels and
transfer its leader bit. The complete table and both queries are preserved. -/
abbrev headerTests : Routine 34 := sequence (relocate RealizabilityCheck.supplyHeader headerRoles)
  (sequence (Compare.preservingEquality 30 levelRoles)
    (sequence (Compare.preservingEquality 30 parentRoles)
      (sequence (move 33 3 34 4) (clearRegisters headerMetadata))))

theorem headerTests_executes (store : Store 34) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (nodes : List Executable.Node) (index : Fin nodes.length)
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val) (level parent : Nat)
    (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 10000*((store 17).length+level.size+parent.size+1)^4,
      Executes headerTests store time
        (Function.update (Function.update (Function.update store 31
          (decide (nodes[index].level=level)::store 31)) 33
          (decide (DagValidation.parentCode nodes[index]=parent)::store 33)) 34
          (nodes[index].leader::store 34)) := by
  let localStore : Store 28 := store ∘ headerRoles
  have localWork (r : Fin 30) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    apply work (headerRoles r) small
    intro equal
    apply different
    exact Fin.ext (congrArg (fun i:Fin 36=>i.val) equal)
  obtain ⟨readTime,readBound,reading⟩ := RealizabilityCheck.supplyHeader_executes localStore accepted tail
    status localWork e19 nodes index suffix input counter
  let node := nodes[index]
  let parsed := parsedHeader store node
  have a : Executes (relocate RealizabilityCheck.supplyHeader headerRoles) store readTime parsed := by
    apply relocate_executes_frame RealizabilityCheck.supplyHeader headerRoles _ _ _ _ readTime rfl _ _ reading
    · intro r;fin_cases r <;> simp [parsed,parsedHeader,RealizabilityCheck.supplyHeaderStore,localStore,headerRoles,node]
    · intro r outside
      have n0 : r≠0 := by intro equal;subst r;exact outside 0 rfl
      have n2 : r≠2 := by intro equal;subst r;exact outside 2 rfl
      have n3 : r≠3 := by intro equal;subst r;exact outside 3 rfl
      have n19 : r≠19 := by intro equal;subst r;exact outside 19 rfl
      simp [parsed,parsedHeader,n0,n2,n3,n19]
  have b := Compare.preservingEquality_executes 30 levelRoles parsed
    (by simp [parsed,parsedHeader,levelRoles,work])
    (by simp [parsed,parsedHeader,levelRoles,work])
    (by simp [parsed,parsedHeader,levelRoles,work])
  have leftLevel : parsed (levelRoles 0)=node.level.bits := rfl
  have rightLevel : parsed (levelRoles 1)=level.bits := by simp [parsed,parsedHeader,levelRoles,levelAt]
  have levelOutput : parsed (levelRoles 2)=store 31 := rfl
  rw [leftLevel,rightLevel,levelOutput] at b
  simp only [Encoding.bits_injective.eq_iff] at b
  let levelTested := Function.update parsed 31 (decide (node.level=level)::store 31)
  have c := Compare.preservingEquality_executes 30 parentRoles levelTested
    (by simp [levelTested,parsed,parsedHeader,parentRoles,work])
    (by simp [levelTested,parsed,parsedHeader,parentRoles,work])
    (by simp [levelTested,parsed,parsedHeader,parentRoles,work])
  have leftParent : levelTested (parentRoles 0)=(DagValidation.parentCode node).bits := by
    simp [levelTested,parsed,parsedHeader,parentRoles]
  have rightParent : levelTested (parentRoles 1)=parent.bits := by
    simp [levelTested,parsed,parsedHeader,parentRoles,parentAt]
  have parentOutput : levelTested (parentRoles 2)=store 33 := by
    simp [levelTested,parsed,parsedHeader,parentRoles]
  rw [leftParent,rightParent,parentOutput] at c
  simp only [Encoding.bits_injective.eq_iff] at c
  let tested := Function.update levelTested 33 (decide (DagValidation.parentCode node=parent)::store 33)
  have d := move_executes 33 (3:Fin 36) 34 4 (by decide) (by decide) (by decide) tested
    (by simp [tested,levelTested,parsed,parsedHeader,work])
  have leaderAt : tested 3=[node.leader] := by simp [tested,levelTested,parsed,parsedHeader]
  have leaderOutput : tested 34=store 34 := by simp [tested,levelTested,parsed,parsedHeader]
  rw [leaderAt,leaderOutput] at d
  let transferred := Function.update (Function.update tested 34 (node.leader::store 34)) 3 []
  have metadataSize := DagValidation.node_metadata_size_le node
  have tailBound := DagValidation.nodeSuffix_length_le node
  have clearBound (r : Fin 36) (member : r∈headerMetadata) :
      (transferred r).length ≤ (Encoding.node.encode node).length := by
    simp only [headerMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · change node.level.bits.length ≤ _;rw [Encoding.bits_length];omega
    · change (DagValidation.parentCode node).bits.length ≤ _;rw [Encoding.bits_length];omega
    · exact tailBound
  obtain ⟨clearTime,clearBound',e⟩ := DagValidation.clear_selected_executes headerMetadata transferred
    (Encoding.node.encode node).length clearBound
  have final : clearedStore headerMetadata transferred=
      Function.update (Function.update (Function.update store 31
        (decide (node.level=level)::store 31)) 33
        (decide (DagValidation.parentCode node=parent)::store 33)) 34 (node.leader::store 34) := by
    funext r;fin_cases r <;>
      simp [clearedStore,headerMetadata,transferred,tested,levelTested,parsed,parsedHeader,work,e19]
  rw [final] at e
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  have nodeLength := DagValidation.node_sequence_member_le nodes node (List.getElem_mem index.isLt)
  have nodeBound : (Encoding.node.encode node).length ≤ (store 17).length := by
    rw [input,List.length_append];omega
  have levelBound := Compare.preservingCost_le node.level.bits level.bits
  have parentBound := Compare.preservingCost_le (DagValidation.parentCode node).bits parent.bits
  simp only [Encoding.bits_length] at levelBound parentBound
  let S := (store 17).length+level.size+parent.size+1
  have raised : ((store 17).length+1)^4 ≤ S^4 := Nat.pow_le_pow_left (by dsimp only [S];omega) 4
  have linear : S ≤ S^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change readTime ≤ 7000*((store 17).length+1)^4 at readBound
  change clearTime ≤ 3*((Encoding.node.encode node).length+2) at clearBound'
  change readTime+1+(Compare.preservingCost node.level.bits level.bits+1+
    (Compare.preservingCost (DagValidation.parentCode node).bits parent.bits+1+
      (6*([node.leader]:List Bool).length+4+1+clearTime))) ≤ 10000*S^4
  simp only [List.length_cons,List.length_nil]
  dsimp only [S] at raised linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
