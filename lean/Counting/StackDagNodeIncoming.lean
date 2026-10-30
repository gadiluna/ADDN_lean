import Counting.StackDagReindexBounds
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def incomingRoles : Fin 40 ↪ Fin 64 := ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,by
  intro a b equal
  apply Fin.ext
  exact congrArg (fun r : Fin 64=>r.val) equal⟩

def buildIncoming : Routine 62 := sequence (pushBit 2 false) (mapRegisters incomingRoles Reindex.incoming)

/-- The edge accumulator is initialized with the actual empty-list header,
then the physical incoming fold runs in a protected node-label workspace. -/
theorem buildIncoming_executes (store : Store 62) (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool)
    (input : store 0=(Encoding.list edgeCodec).encode node.incoming++suffix)
    (mapInput : store 1=(Encoding.array Encoding.natural).encode mapping)
    (empty : ∀ r : Fin 64,2 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 200000000*((store 0).length+(store 1).length+2)^7+2,
      Executes buildIncoming store time (Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (Executable.referenceMap mapping node).incoming)) := by
  have starting:=pushBit_executes (2:Fin 64) false store
  rw [empty 2 (by decide) (by decide)] at starting
  let ready:=Function.update store 2 [false]
  let localStore : Store 38:=ready ∘ incomingRoles
  have localWork (r : Fin 40) (lower : 3 ≤ r.val) (upper : r.val ≤ 37) : localStore r=[] := by
    have ne : incomingRoles r≠2 := by intro equal;have value:=congrArg (fun r : Fin 64=>r.val) equal;dsimp [incomingRoles] at value;omega
    simpa [localStore,ready,Function.comp_apply,ne] using empty (incomingRoles r) (by exact Nat.le_trans (by decide) lower) upper
  obtain ⟨time,bound,ran⟩:=Reindex.incoming_executes_polynomial localStore mapping.toList node.incoming [] suffix
    (by simpa [localStore,ready,incomingRoles] using input)
    (by simpa [localStore,ready,incomingRoles,Encoding.array,Encoding.transport] using mapInput)
    (by rfl) localWork
  have same : Reindex.remap mapping.toList=(fun acc edge=>Executable.addCount (mapping[edge.1]?.getD 0) edge.2 acc) := by
    funext acc edge
    simp [Reindex.remap]
  rw [same] at ran
  let target:=Function.update (Function.update store 0 suffix) 2
    ((Encoding.list edgeCodec).encode (Executable.referenceMap mapping node).incoming)
  have relocated : Executes (mapRegisters incomingRoles Reindex.incoming) ready time target := by
    apply relocate_executes_frame Reindex.incoming incomingRoles ready target localStore
      (Function.update (Function.update localStore 0 suffix) 2
        ((Encoding.list edgeCodec).encode (Executable.referenceMap mapping node).incoming)) time rfl _ _ ran
    · intro r
      by_cases r0 : r=0
      · subst r;simp [target,incomingRoles]
      · by_cases r2 : r=2
        · subst r;simp [target,incomingRoles]
        · have n0 : incomingRoles r≠0 := by intro equal;apply r0;apply Fin.ext;exact congrArg (fun r : Fin 64=>r.val) equal
          have n2 : incomingRoles r≠2 := by intro equal;apply r2;apply Fin.ext;exact congrArg (fun r : Fin 64=>r.val) equal
          simp [target,localStore,ready,Function.comp_apply,r0,r2,n0,n2]
    · intro r outside
      have n0 : r≠0 := fun eq=>outside 0 (by simpa [incomingRoles] using eq.symm)
      have n2 : r≠2 := fun eq=>outside 2 (by simpa [incomingRoles] using eq.symm)
      simp [target,ready,n0,n2]
  have inputAt : localStore 0=store 0 := by simp [localStore,ready,incomingRoles]
  have mapAt : localStore 1=store 1 := by simp [localStore,ready,incomingRoles]
  have accumulatorAt : localStore 2=[false] := by simp [localStore,ready,incomingRoles]
  rw [inputAt,mapAt,accumulatorAt] at bound
  simp only [List.length_cons,List.length_nil] at bound
  refine ⟨1+1+time,?_,starting.sequence relocated⟩
  change time ≤ 200000000*((store 0).length+(store 1).length+2)^7 at bound
  omega

end Counting.StackMachine.DagUpdate.NodeMap
