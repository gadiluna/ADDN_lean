import Counting.StackRealizabilityInputSplit
import Counting.StackDagPasses

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def inputValidationRoles : Fin 37 ↪ Fin 100 :=
  ⟨![0,85,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,99,36],by decide⟩

def inputValidate : Routine 98 := mapRegisters inputValidationRoles DagValidation.semanticRoutine

/-- The semantic DAG validator acts on the vista physically extracted
from the canonical verifier tuple. Counts, order, leader count and the
original vista encoding remain unchanged. -/
theorem inputValidate_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 224000000*((Encoding.vista.encode vista).length+1)^6,
      Executes inputValidate (inputFieldsStore vista values ell order (accepted::tail)) time
        (inputFieldsStore vista values ell order ((accepted && vista.valid)::tail)) := by
  obtain ⟨time,bound,run⟩ := DagValidation.semanticRoutine_executes vista accepted tail
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame DagValidation.semanticRoutine inputValidationRoles
    (inputFieldsStore vista values ell order (accepted::tail))
    (inputFieldsStore vista values ell order ((accepted && vista.valid)::tail))
    (DagValidation.validatorStore (Encoding.vista.encode vista) (accepted::tail))
    (DagValidation.validatorStore (Encoding.vista.encode vista) ((accepted && vista.valid)::tail))
    time _ _ _ run
  · funext r
    fin_cases r <;> simp [inputFieldsStore,inputValidationRoles,DagValidation.validatorStore]
  · intro r
    fin_cases r <;> simp [inputFieldsStore,inputValidationRoles,DagValidation.validatorStore]
  · intro r outside
    have different : r≠85 := by intro same;subst r;exact outside 1 rfl
    simp [inputFieldsStore,different]

end Counting.StackMachine.RealizabilityCheck
