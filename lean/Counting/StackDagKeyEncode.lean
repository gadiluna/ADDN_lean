import Counting.StackDagNodeLabels
import Counting.StackDagKeyLeader
import Counting.StackEncodingFrameStore
import Counting.StackRoutineMove
import Counting.DagKeyEncoding

namespace Counting.StackMachine.DagUpdate.Key
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Emit the exact numeric key as a self-delimiting sequence. Its length
header is unnecessary for the comparison routine, which scans this word. -/
def encodeKey : Routine 62 := sequence NodeMap.readLabels
  (sequence (ofProgram (unframeProgram 61 0 44 49))
    (sequence (clear 44) (sequence (move 61 0 3 49)
      (sequence (frameRoutine 61 43 3 49) (sequence (frameRoutine 61 41 3 49)
        (sequence (emitLeader 42 3) (frameRoutine 61 40 3 49)))))))

def keyBudget (node : Executable.Node) : Nat :=
  10*(node.level.bits.length+(NodeMap.parentNumber node).bits.length+node.degree.bits.length)+
    6*node.incoming.length.bits.length+
    6*(Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming).length+
    2*(Encoding.natural.encode (if node.leader then 1 else 0)).length+38

theorem encodeKey_executes (store : Store 62) (node : Executable.Node)
    (source : store 0=Encoding.node.encode node)
    (empty : ∀ r : Fin 64,r=3 ∨ (40 ≤ r.val ∧ r.val ≤ 44) ∨ r=49 → store r=[]) :
    Executes encodeKey store (keyBudget node)
      (Function.update (Function.update store 0 []) 3 (Encoding.sequence Encoding.natural node.key)) := by
  have labels := NodeMap.readLabels_executes store node [] (by simpa using source)
    (fun r lower upper=>empty r (Or.inr (Or.inl ⟨lower,upper⟩)))
  let stream := Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming
  let read := NodeMap.labelsResult store node []
  have header := unframe_canonical_executes 61 (0:Fin 64) 44 49 (by decide) (by decide) (by decide)
    read node.incoming.length.bits stream (by
      simp [read,NodeMap.labelsResult,Encoding.list,Encoding.natural,stream])
    (by simp [read,NodeMap.labelsResult,empty])
  have headerEmpty : read 44=[] := by simp [read,NodeMap.labelsResult,empty]
  rw [headerEmpty,List.append_nil] at header
  let counted := Function.update (Function.update read 0 stream) 44 node.incoming.length.bits
  have erase := clear_executes (44:Fin 64) counted
  have countAt : counted 44=node.incoming.length.bits := by simp [counted]
  rw [countAt] at erase
  let stripped := Function.update counted 44 []
  have moveStream := move_executes 61 (0:Fin 64) 3 49 (by decide) (by decide) (by decide)
    stripped (by simp [stripped,counted,read,NodeMap.labelsResult,empty])
  have streamAt : stripped 0=stream := by simp [stripped,counted]
  have targetEmpty : stripped 3=[] := by simp [stripped,counted,read,NodeMap.labelsResult,empty]
  rw [streamAt,targetEmpty,List.append_nil] at moveStream
  let moved := Function.update (Function.update stripped 3 stream) 0 []
  have degree := frame_executes_updates 61 (43:Fin 64) 3 49 (by decide) (by decide) (by decide)
    moved (by simp [moved,stripped,counted,read,NodeMap.labelsResult,empty])
  have degreeAt : moved 43=node.degree.bits := by simp [moved,stripped,counted,read,NodeMap.labelsResult]
  have firstTarget : moved 3=stream := by simp [moved]
  rw [degreeAt,firstTarget] at degree
  let degreeRead := Function.update (Function.update moved 43 []) 3 (Encoding.frame node.degree.bits++stream)
  have parent := frame_executes_updates 61 (41:Fin 64) 3 49 (by decide) (by decide) (by decide)
    degreeRead (by simp [degreeRead,moved,stripped,counted,read,NodeMap.labelsResult,empty])
  have parentAt : degreeRead 41=(NodeMap.parentNumber node).bits := by
    simp [degreeRead,moved,stripped,counted,read,NodeMap.labelsResult]
  have secondTarget : degreeRead 3=Encoding.frame node.degree.bits++stream := by simp [degreeRead]
  rw [parentAt,secondTarget] at parent
  let parentRead := Function.update (Function.update degreeRead 41 []) 3
    (Encoding.frame (NodeMap.parentNumber node).bits++(Encoding.frame node.degree.bits++stream))
  have leader := emitLeader_executes (42:Fin 64) 3 (by decide) parentRead node.leader
    (by simp [parentRead,degreeRead,moved,stripped,counted,read,NodeMap.labelsResult])
  have thirdTarget : parentRead 3=Encoding.frame (NodeMap.parentNumber node).bits++
      (Encoding.frame node.degree.bits++stream) := by simp [parentRead]
  rw [thirdTarget] at leader
  let leaderRead := Function.update (Function.update parentRead 42 []) 3
    (Encoding.natural.encode (if node.leader then 1 else 0)++
      (Encoding.frame (NodeMap.parentNumber node).bits++(Encoding.frame node.degree.bits++stream)))
  have level := frame_executes_updates 61 (40:Fin 64) 3 49 (by decide) (by decide) (by decide)
    leaderRead (by simp [leaderRead,parentRead,degreeRead,moved,stripped,counted,read,NodeMap.labelsResult,empty])
  have levelAt : leaderRead 40=node.level.bits := by
    simp [leaderRead,parentRead,degreeRead,moved,stripped,counted,read,NodeMap.labelsResult]
  have fourthTarget : leaderRead 3=Encoding.natural.encode (if node.leader then 1 else 0)++
      (Encoding.frame (NodeMap.parentNumber node).bits++(Encoding.frame node.degree.bits++stream)) := by
    simp [leaderRead]
  rw [levelAt,fourthTarget] at level
  have final : Function.update (Function.update leaderRead 40 []) 3
      (Encoding.frame node.level.bits++(Encoding.natural.encode (if node.leader then 1 else 0)++
        (Encoding.frame (NodeMap.parentNumber node).bits++(Encoding.frame node.degree.bits++stream))))=
      Function.update (Function.update store 0 []) 3 (Encoding.sequence Encoding.natural node.key) := by
    rw [Executable.sequence_key]
    funext r
    fin_cases r <;> simp [leaderRead,parentRead,degreeRead,moved,stripped,counted,read,
      NodeMap.labelsResult,Encoding.natural,NodeMap.parentNumber,
      stream,List.append_assoc,empty]
  rw [final] at level
  have executed := labels.sequence (header.sequence (erase.sequence (moveStream.sequence
    (degree.sequence (parent.sequence (leader.sequence level))))))
  convert executed using 1 <;> first | rfl | (dsimp only [keyBudget,stream];omega)

end Counting.StackMachine.DagUpdate.Key
