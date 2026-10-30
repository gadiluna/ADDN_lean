import Counting.StackRealizabilityInputCount
import Counting.StackRealizabilityBottom

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def inputBottomRoles : Fin 9 ↪ Fin 100 := ⟨![81,87,85,0,1,2,3,4,5],by decide⟩
def inputBottom : Routine 98 := mapRegisters inputBottomRoles countOneGuard

theorem inputBottom_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (length : values.length=vista.nodes.size)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 60*(((Encoding.list Encoding.natural).encode values).length+vista.nodes.size+1),
      Executes inputBottom (inputCountStore vista values ell order (accepted::tail)) time
        (inputCountStore vista values ell order
          ((accepted && decide (RealizabilityVerifier.weight values.toArray vista.bottom=1))::tail)) := by
  let start := inputCountStore vista values ell order (accepted::tail)
  let localStore : Store 7 := start ∘ inputBottomRoles
  obtain ⟨time,bound,run⟩ := countOneGuard_bottom_executes localStore accepted tail
    (by simp [localStore,start,inputBottomRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by intro i large;fin_cases i <;> simp_all [localStore,start,inputBottomRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    vista valid values.toArray (by simpa only [List.size_toArray] using length)
    (by simp [localStore,start,inputBottomRoles,inputCountStore,inputNodesStore,inputFieldsStore])
    (by simp [localStore,start,inputBottomRoles,inputCountStore,length])
  refine ⟨time,?_,?_⟩
  · simpa [localStore,start,inputBottomRoles,inputCountStore,inputNodesStore,inputFieldsStore,length] using bound
  · apply relocate_executes_frame countOneGuard inputBottomRoles start _ localStore _ time rfl _ _ run
    · intro i
      fin_cases i <;> simp [localStore,start,inputBottomRoles,inputCountStore,inputNodesStore,inputFieldsStore]
    · intro i outside
      have different:i≠85 := by intro same;subst i;exact outside 2 rfl
      by_cases a:i=87 <;> by_cases b:i=80 <;>
        simp_all [start,inputCountStore,inputNodesStore,inputFieldsStore]

end Counting.StackMachine.RealizabilityCheck
