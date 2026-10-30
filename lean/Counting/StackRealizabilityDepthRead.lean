import Counting.StackRealizabilityDepthPrepare
import Counting.StackRealizabilityInitialHeader
import Counting.StackRealizabilityBottom

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def depthReadRoles : Fin 26 ↪ Fin 100 :=
  ⟨![74,85,75,76,4,5,6,7,8,9,10,11,12,13,14,15,16,70,73,77,20,21,22,23,24,25],by decide⟩
def depthRead : Routine 98 := mapRegisters depthReadRoles initialHeader

def depthMetadataStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  let node := vista.node vista.bottom
  Function.update (Function.update (Function.update (Function.update
    (depthPreparedStore vista values ell order status) 74 node.level.bits)
    75 (DagValidation.parentCode node).bits) 76 [node.leader]) 77 (DagValidation.nodeSuffix node)

/-- The depth is read from the final actual serialized node. Validity
identifies that entry with the bottom; the index is the copied table count. -/
theorem depthRead_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 7000*((Encoding.sequence Encoding.node vista.nodes.toList).length+1)^4,
      Executes depthRead (depthPreparedStore vista values ell order (accepted::tail)) time
        (depthMetadataStore vista values ell order (accepted::tail)) := by
  have last := valid_bottom_last vista valid
  have inside : vista.bottom<vista.nodes.size := by omega
  let position : Fin vista.nodes.toList.length := ⟨vista.bottom,by simpa only [Array.length_toList] using inside⟩
  have selected : vista.nodes.toList[position]=vista.node vista.bottom := by
    simp [position,Executable.Vista.node,inside]
  let start := depthPreparedStore vista values ell order (accepted::tail)
  let localStore : Store 24 := start ∘ depthReadRoles
  obtain ⟨time,bound,run⟩ := initialHeader_executes localStore accepted tail
    (by simp [localStore,start,depthReadRoles,depthPreparedStore,inputCountStore,inputNodesStore,inputFieldsStore])
    (by intro i small different;fin_cases i <;>
      simp_all [localStore,start,depthReadRoles,depthPreparedStore,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,start,depthReadRoles,depthPreparedStore,inputCountStore,inputNodesStore,inputFieldsStore])
    vista.nodes.toList position [] (by simp [localStore,start,depthReadRoles,depthPreparedStore])
    (by simp [localStore,start,depthReadRoles,depthPreparedStore,position];omega)
  rw [selected] at run
  refine ⟨time,?_,?_⟩
  · simpa [localStore,start,depthReadRoles,depthPreparedStore] using bound
  · apply relocate_executes_frame initialHeader depthReadRoles start _ localStore
      (initialHeaderStore localStore (vista.node vista.bottom)) time rfl _ _ run
    · intro i
      fin_cases i <;> simp [localStore,start,depthReadRoles,depthMetadataStore,initialHeaderStore,
        depthPreparedStore,inputCountStore,inputNodesStore,inputFieldsStore]
    · intro i outside
      have n74:i≠74 := by intro same;subst i;exact outside 0 rfl
      have n75:i≠75 := by intro same;subst i;exact outside 2 rfl
      have n76:i≠76 := by intro same;subst i;exact outside 3 rfl
      have n77:i≠77 := by intro same;subst i;exact outside 19 rfl
      simp [depthMetadataStore,start,n74,n75,n76,n77]

end Counting.StackMachine.RealizabilityCheck
