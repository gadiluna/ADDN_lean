import Counting.StackAuditPrefixHeader
import Counting.StackAuditPrefixLabelGuards
import Counting.DagClosureCriterion
import Counting.RealizabilityVerifierTransport

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def depthHeaderRoles : Fin 30 ↪ Fin 52 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b same;exact Fin.ext (congrArg (fun r:Fin 52=>r.val) same)⟩
def depthCompareRoles : Fin 6 ↪ Fin 52 := ⟨![39,0,1,4,5,6],by decide⟩
def depthMetadata : List (Fin 52) := [0,2,3,18,19]

abbrev checkDepth : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 20 18 51))
  (sequence (discardBit 18)
    (sequence (relocate RealizabilityCheck.supplyHeader depthHeaderRoles)
      (sequence (Binary.preservingComparison 46 depthCompareRoles)
        (sequence (ofProgram (combineFlagsProgram 50 1)) (clearRegisters depthMetadata)))))

theorem valid_bottom_last (vista : Executable.Vista) (valid : vista.valid=true) :
    vista.bottom+1=vista.nodes.size :=
  (Executable.backwardCover_of_allReachable vista (Executable.topological_of_valid vista valid)
    (RealizabilityVerifier.bottom_inside vista valid) (Executable.allReachable_of_valid vista valid)).1

def depthParsed (store : Store 50) (node : Executable.Node) : Store 50 :=
  fun r=>if r=0 then node.level.bits else if r=2 then (DagValidation.parentCode node).bits
    else if r=3 then [node.leader] else if r=19 then DagValidation.nodeSuffix node else store r

/-- After validation, the actual last stored node is the bottom. Its unary
lookup index is copied from the physical node budget, never from a label. -/
theorem checkDepth_executes (store : Store 50) (vista : Executable.Vista) (valid : vista.valid=true)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e51 : store 51=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (last : Nat) (lastAt : store 39=last.bits) :
    ∃ time ≤ 10000*((store 17).length+last.size+1)^4,
      Executes checkDepth store time (Function.update store 1
        ((accepted && decide (last≤(vista.node vista.bottom).level))::tail)) := by
  have bottomLast:=valid_bottom_last vista valid
  have inside:=RealizabilityVerifier.bottom_inside vista valid
  let index:Fin vista.nodes.toList.length:=⟨vista.bottom,by simpa using inside⟩
  let node:=vista.node vista.bottom
  have nodeSame : vista.nodes.toList[index]=node := by
    simp [index,node,Executable.Vista.node,Array.getElem?_eq_getElem inside]
  have a:=copy_executes 49 (20:Fin 52) 18 51 (by decide) (by decide) (by decide) store e51
  rw [nodeCount,e18,List.append_nil,List.length_replicate] at a
  let copied:=Function.update store 18 (List.replicate vista.nodes.size true)
  have b:=discardBit_executes (18:Fin 52) copied
  have countTail : (copied 18).tail=List.replicate vista.bottom true := by
    simp [copied,←bottomLast,List.replicate_succ]
  rw [countTail] at b
  let indexed:=Function.update store 18 (List.replicate vista.bottom true)
  have bResult : Function.update copied 18 (List.replicate vista.bottom true)=indexed := by
    simp [copied,indexed]
  rw [bResult] at b
  let localStore:Store 28:=indexed ∘ depthHeaderRoles
  have localWork (r:Fin 30) (small:r.val<17) (different:r≠1) : localStore r=[] := by
    have diff:depthHeaderRoles r≠1 := by
      intro equal;apply different;exact Fin.ext (congrArg (fun q:Fin 52=>q.val) equal)
    have diff18:depthHeaderRoles r≠18 := by
      intro equal;have:=congrArg (fun q:Fin 52=>q.val) equal
      simp only [depthHeaderRoles,Function.Embedding.coeFn_mk] at this
      omega
    simpa [localStore,indexed,diff18] using work (depthHeaderRoles r) small diff
  obtain ⟨headerTime,headerBound,c⟩:=RealizabilityCheck.supplyHeader_executes localStore accepted tail
    (by simp [localStore,indexed,depthHeaderRoles,status]) localWork
    (by simp [localStore,indexed,depthHeaderRoles,e19]) vista.nodes.toList index suffix
    (by simp [localStore,indexed,depthHeaderRoles,source])
    (by simp [localStore,indexed,depthHeaderRoles,index])
  rw [nodeSame] at c
  let parsed:=depthParsed indexed node
  have header : Executes (relocate RealizabilityCheck.supplyHeader depthHeaderRoles) indexed headerTime parsed := by
    apply relocate_executes_frame RealizabilityCheck.supplyHeader depthHeaderRoles indexed parsed
      localStore _ headerTime rfl _ _ c
    · intro r;fin_cases r <;> simp [parsed,depthParsed,depthHeaderRoles,localStore,RealizabilityCheck.supplyHeaderStore]
    · intro r outside
      have n0:r≠0 := by intro equal;subst r;exact outside 0 rfl
      have n2:r≠2 := by intro equal;subst r;exact outside 2 rfl
      have n3:r≠3 := by intro equal;subst r;exact outside 3 rfl
      have n19:r≠19 := by intro equal;subst r;exact outside 19 rfl
      simp [parsed,depthParsed,n0,n2,n3,n19]
  have d:=Binary.preservingComparison_executes 46 depthCompareRoles parsed
    (by simp [depthCompareRoles,parsed,depthParsed,indexed,work])
    (by simp [depthCompareRoles,parsed,depthParsed,indexed,work])
    (by simp [depthCompareRoles,parsed,depthParsed,indexed,work])
  have first : parsed (depthCompareRoles 0)=last.bits := by
    simp [depthCompareRoles,parsed,depthParsed,indexed,lastAt]
  have second : parsed (depthCompareRoles 1)=node.level.bits := by simp [depthCompareRoles,parsed,depthParsed]
  have oldFlag : parsed (depthCompareRoles 2)=accepted::tail := by
    simp [depthCompareRoles,parsed,depthParsed,indexed,status]
  rw [first,second,oldFlag] at d
  have comparison : Binary.compareBits true last.bits node.level.bits=decide (last≤node.level) := by
    apply Bool.eq_iff_iff.mpr;simp [Binary.compareBits_le,Encoding.value_bits]
  rw [comparison] at d
  let tested:=Function.update parsed 1 (decide (last≤node.level)::accepted::tail)
  have e:=combineFlags_executes 50 (1:Fin 52) tested accepted (decide (last≤node.level)) tail
    (by simp [tested])
  let checked:=Function.update parsed 1 ((accepted && decide (last≤node.level))::tail)
  have eResult : Function.update tested 1 ((accepted && decide (last≤node.level))::tail)=checked := by
    simp [tested,checked]
  rw [eResult] at e
  have nodeLength:=DagValidation.node_sequence_member_le vista.nodes.toList node
    (by rw [←nodeSame];exact List.getElem_mem index.isLt)
  have nodeBound : (Encoding.node.encode node).length≤(store 17).length := by
    rw [source,List.length_append];omega
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  have countBound : vista.nodes.size≤(store 17).length := by
    rw [source,List.length_append];simp only [Array.length_toList] at nodes;omega
  have metadata:=DagValidation.node_metadata_size_le node
  have suffixBound:=DagValidation.nodeSuffix_length_le node
  obtain ⟨cleanTime,cleanBound,f⟩:=DagValidation.clear_selected_executes depthMetadata checked
    (store 17).length (by
      intro r member
      simp only [depthMetadata,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl
      · change node.level.bits.length≤_;rw [Encoding.bits_length];omega
      · change (DagValidation.parentCode node).bits.length≤_;rw [Encoding.bits_length];omega
      · change (1:Nat)≤_;omega
      · change (List.replicate vista.bottom true).length≤_;rw [List.length_replicate];omega
      · change (DagValidation.nodeSuffix node).length≤_;omega)
  have final : clearedStore depthMetadata checked=Function.update store 1
      ((accepted && decide (last≤node.level))::tail) := by
    funext r;fin_cases r <;> simp [clearedStore,depthMetadata,checked,parsed,depthParsed,indexed,work,e18,e19]
  rw [final] at f
  have tableAt : (localStore 17).length=(store 17).length := by simp [localStore,indexed,depthHeaderRoles]
  rw [tableAt] at headerBound
  have compareBound:=Binary.preservingCompareCost_le last.bits node.level.bits
  simp only [Encoding.bits_length] at compareBound
  let S:=(store 17).length+last.size+1
  have raised:=headerBound.trans (Nat.mul_le_mul_left 7000 (Nat.pow_le_pow_left
    (by dsimp only [S];omega : (store 17).length+1≤S) 4))
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  have one : 1≤S^4:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change cleanTime≤5*((store 17).length+2) at cleanBound
  refine ⟨_,?_,a.sequence (b.sequence (header.sequence (d.sequence (e.sequence f))))⟩
  change 5*vista.nodes.size+2+1+(1+1+(headerTime+1+
    (Binary.preservingCompareCost last.bits node.level.bits+1+(3+1+cleanTime))))≤10000*S^4
  dsimp only [S] at raised linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
