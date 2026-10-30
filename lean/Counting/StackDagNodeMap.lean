import Counting.StackDagNodeParent
import Counting.StackDagNodeIncoming
import Counting.StackDagNodeAssemble

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Remap the parent and incoming references of one compact, serialized node.
The input mapping and every register outside the workspace are preserved. -/
def referenceMap : Routine 62 :=
  sequence readLabels (sequence buildParent (sequence buildIncoming assemble))

def referenceMapBudget (mapping : Array Nat) (node : Executable.Node) (suffix : List Bool) : Nat :=
  let target := Executable.referenceMap mapping node
  5*(node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length)+11+
  2100*(((Encoding.array Encoding.natural).encode mapping).length+(parentNumber node).size+1)^3+
  (200000000*(((Encoding.list edgeCodec).encode node.incoming).length+suffix.length+
    ((Encoding.array Encoding.natural).encode mapping).length+2)^7+2)+
  (9*(target.level.bits.length+(parentNumber target).bits.length+target.degree.bits.length)+
    2*((Encoding.list edgeCodec).encode target.incoming).length+
    2*(Encoding.node.encode target).length+(parentNumber node).bits.length+35)+3

/-- The code traverses only the compact encoding; large binary multiplicities
and missing references are handled with the exact executable semantics. -/
theorem referenceMap_executes (store : Store 62) (mapping : Array Nat)
    (node : Executable.Node) (suffix : List Bool)
    (input : store 0=Encoding.node.encode node++suffix)
    (mapInput : store 1=(Encoding.array Encoding.natural).encode mapping)
    (empty : ∀ r : Fin 64,2 ≤ r.val → r.val ≤ 48 → store r=[]) :
    ∃ time ≤ referenceMapBudget mapping node suffix,
      Executes referenceMap store time
        (Function.update (Function.update store 0 suffix) 3
          (Encoding.node.encode (Executable.referenceMap mapping node))) := by
  let target := Executable.referenceMap mapping node
  let labels := labelsResult store node suffix
  let parent := Function.update labels 45 (parentNumber target).bits
  let incoming := Function.update (Function.update parent 0 suffix) 2
    ((Encoding.list edgeCodec).encode target.incoming)
  have read := readLabels_executes store node suffix input
    (fun r lower upper=>empty r (by omega) (by omega))
  obtain ⟨parentTime,parentBound,parentRun⟩ := buildParent_executes labels mapping node
    (by simpa [labels,labelsResult] using mapInput)
    (by simp [labels,labelsResult]) (by
      intro r eligible
      fin_cases r <;> simp_all [labels,labelsResult])
  obtain ⟨incomingTime,incomingBound,incomingRun⟩ := buildIncoming_executes parent mapping node suffix
    (by simp [parent,labels,labelsResult,edgeCodec])
    (by simpa [parent,labels,labelsResult] using mapInput) (by
      intro r lower upper
      fin_cases r <;> simp_all [parent,labels,labelsResult])
  have assembled := assemble_executes incoming target
    (by simp [incoming,parent,labels,labelsResult,target,Executable.referenceMap])
    (by simp [incoming,parent])
    (by simp [incoming,parent,labels,labelsResult,target,Executable.referenceMap])
    (by simp [incoming,parent,labels,labelsResult,target,Executable.referenceMap])
    (by rfl)
    (by simp [incoming,parent,labels,labelsResult,empty])
    (by simp [incoming,parent,labels,labelsResult,empty])
    (by simp [incoming,parent,labels,labelsResult,empty])
    (by simp [incoming,parent,labels,labelsResult,empty])
  have final : assembledResult incoming target=
      Function.update (Function.update store 0 suffix) 3 (Encoding.node.encode target) := by
    funext r
    fin_cases r <;> simp [assembledResult,incoming,parent,labels,labelsResult,empty]
  rw [final] at assembled
  have ran := read.sequence (parentRun.sequence (incomingRun.sequence assembled))
  refine ⟨_,?_,ran⟩
  have mappingAt : labels 1=(Encoding.array Encoding.natural).encode mapping := by
    simpa [labels,labelsResult] using mapInput
  have sourceAt : parent 0=(Encoding.list edgeCodec).encode node.incoming++suffix := by
    simp [parent,labels,labelsResult,edgeCodec]
  have parentMappingAt : parent 1=(Encoding.array Encoding.natural).encode mapping := by
    simpa [parent,labels,labelsResult] using mapInput
  have oldParentAt : incoming 41=(parentNumber node).bits := by
    simp [incoming,parent,labels,labelsResult]
  rw [mappingAt] at parentBound
  rw [sourceAt,parentMappingAt,List.length_append] at incomingBound
  rw [oldParentAt]
  dsimp only [referenceMapBudget,target,edgeCodec]
  dsimp only [edgeCodec] at incomingBound
  omega

end Counting.StackMachine.DagUpdate.NodeMap
