import Counting.StackAuditPropagationAnchorLoop
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def anchorStageRoles : Fin 37 ↪ Fin 44 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 44=>r.val) equal)⟩

abbrev anchorStage : Routine 42 := relocate anchorLoop anchorStageRoles

def assigned (vista : Executable.Vista) (anchor : Nat) (values : Array Nat) : Array Nat :=
  Executable.assignEntries ((Executable.levelNodes vista anchor).zip values.toList) (Array.replicate vista.nodes.size 0)

def anchorStageStore (store : Store 42) (vista : Executable.Vista) (anchor : Nat) (values : Array Nat) : Store 42 :=
  Function.update (Function.update (Function.update (Function.update store 32 []) 18
    (List.replicate vista.nodes.size true)) 36
      (Encoding.sequence Encoding.natural (remainingValues anchor vista.nodes.toList values.toList))) 35
        ((Encoding.array Encoding.natural).encode (assigned vista anchor values))

/-- Integration interface for the real anchor scan in the propagation bank.
The selected node list and initial zeros are exactly those of the executable. -/
theorem anchorStage_executes (store : Store 42) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 44,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e21 : store 21=[]) (e31 : store 31=[])
    (vista : Executable.Vista) (anchor : Nat) (values : Array Nat)
    (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (query : store 30=anchor.bits)
    (array : store 35=(Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0))
    (source : store 36=Encoding.sequence Encoding.natural values.toList)
    (counter : store 32=List.replicate vista.nodes.size true) :
    ∃ time ≤ vista.nodes.size*(9000*((store 17).length+(store 35).length+(store 36).length+
        anchor.size+vista.nodes.size+1)^4+2)+1,
      Executes anchorStage store time (anchorStageStore store vista anchor values) := by
  let localStore : Store 35 := store ∘ anchorStageRoles
  have localWork (r : Fin 37) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    apply work (anchorStageRoles r) small
    intro equal;apply different
    exact Fin.ext (congrArg (fun i:Fin 44=>i.val) equal)
  obtain ⟨time,bounded,body⟩ := anchorLoop_executes localStore accepted tail status localWork e19 e21 e31
    vista.nodes.toList vista.nodes.toList 0 (by omega) (by intro i hi;simp only [Nat.zero_add])
    (Encoding.natural.encode vista.bottom) input e18 anchor query (Array.replicate vista.nodes.size 0)
    (by simp) array values.toList source (List.replicate vista.nodes.size true) counter (by simp)
  refine ⟨time,?_,?_⟩
  · simpa [localStore,anchorStageRoles] using bounded
  · apply relocate_executes_frame anchorLoop anchorStageRoles _ _ _ _ time rfl _ _ body
    · intro r;fin_cases r <;>
        simp [anchorStageStore,anchorLoopStore,localStore,anchorStageRoles,assigned,assignScan_vista]
    · intro r outside
      have n18 : r≠18 := by intro same;subst r;exact outside 18 rfl
      have n32 : r≠32 := by intro same;subst r;exact outside 32 rfl
      have n35 : r≠35 := by intro same;subst r;exact outside 35 rfl
      have n36 : r≠36 := by intro same;subst r;exact outside 36 rfl
      simp [anchorStageStore,n18,n32,n35,n36]

end Counting.StackMachine.AuditPropagation
