import Counting.StackUnframeCanonical
import Counting.StackRoutineReadBit
import Counting.EncodingDag

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def parentNumber (node : Executable.Node) : Nat := (node.parent.map (·+1)).getD 0

def readLabels : Routine 62 :=
  sequence (ofProgram (unframeProgram 61 0 40 44))
    (sequence (ofProgram (unframeProgram 61 0 41 44))
      (sequence (readBit 0 42) (ofProgram (unframeProgram 61 0 43 44))))

def labelsResult (store : Store 62) (node : Executable.Node) (suffix : List Bool) : Store 62 :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    0 ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix))
    40 node.level.bits) 41 (parentNumber node).bits) 42 [node.leader]) 43 node.degree.bits

theorem readLabels_executes (store : Store 62) (node : Executable.Node) (suffix : List Bool)
    (input : store 0=Encoding.node.encode node++suffix)
    (empty : ∀ r : Fin 64,40 ≤ r.val → r.val ≤ 44 → store r=[]) :
    Executes readLabels store
      (5*(node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length)+11)
      (labelsResult store node suffix) := by
  let incoming:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming++suffix
  let afterParent:=node.leader::(Encoding.frame node.degree.bits++incoming)
  let afterLevel:=Encoding.frame (parentNumber node).bits++afterParent
  have first:=unframe_canonical_executes 61 (0:Fin 64) 40 44 (by decide) (by decide) (by decide)
    store node.level.bits afterLevel (by
      simpa [Encoding.node,Encoding.transport,Encoding.nodeFields,Encoding.product,Encoding.natural,
        Encoding.optionalNatural,Encoding.boolean,parentNumber,afterLevel,afterParent,incoming,List.append_assoc] using input)
    (empty 44 (by decide) (by decide))
  rw [empty 40 (by decide) (by decide),List.append_nil] at first
  let levelRead:=Function.update (Function.update store 0 afterLevel) 40 node.level.bits
  have second:=unframe_canonical_executes 61 (0:Fin 64) 41 44 (by decide) (by decide) (by decide)
    levelRead (parentNumber node).bits afterParent (by simp [levelRead,afterLevel]) (by simp [levelRead,empty])
  have parentEmpty : levelRead 41=[] := by simp [levelRead,empty]
  rw [parentEmpty,List.append_nil] at second
  let parentRead:=Function.update (Function.update levelRead 0 afterParent) 41 (parentNumber node).bits
  have leader:=readBit_executes (0:Fin 64) 42 (by decide) parentRead node.leader
    (Encoding.frame node.degree.bits++incoming) (by simp [parentRead,afterParent])
  have leaderEmpty : parentRead 42=[] := by simp [parentRead,levelRead,empty]
  rw [leaderEmpty] at leader
  let leaderRead:=Function.update (Function.update parentRead 0 (Encoding.frame node.degree.bits++incoming)) 42 [node.leader]
  have last:=unframe_canonical_executes 61 (0:Fin 64) 43 44 (by decide) (by decide) (by decide)
    leaderRead node.degree.bits incoming (by simp [leaderRead]) (by simp [leaderRead,parentRead,levelRead,empty])
  have degreeEmpty : leaderRead 43=[] := by simp [leaderRead,parentRead,levelRead,empty]
  rw [degreeEmpty,List.append_nil] at last
  have final : Function.update (Function.update leaderRead 0 incoming) 43 node.degree.bits=labelsResult store node suffix := by
    funext r
    by_cases r0 : r=0
    · subst r;simp [labelsResult,incoming]
    · by_cases r40 : r=40 <;> by_cases r41 : r=41 <;> by_cases r42 : r=42 <;> by_cases r43 : r=43 <;>
        simp [labelsResult,leaderRead,parentRead,levelRead,r0,r40,r41,r42,r43]
  rw [final] at last
  have ran:=first.sequence (second.sequence (leader.sequence last))
  convert ran using 1 <;> first | rfl | omega

end Counting.StackMachine.DagUpdate.NodeMap
