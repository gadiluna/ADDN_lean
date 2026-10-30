import Counting.StackRoutineRelocate

namespace Counting.StackMachine.Routine

theorem relocatedStore_eq {registers targets : Nat} (address : Fin registers ↪ Fin targets)
    (base target : Fin targets → List Bool) (localStore : Fin registers → List Bool)
    (inside : ∀ source, target (address source) = localStore source)
    (outside : ∀ register, (∀ source, address source ≠ register) → target register = base register) :
    relocatedStore address base localStore = target := by
  funext register
  by_cases member : ∃ source, address source = register
  · obtain ⟨source,rfl⟩ := member
    rw [relocatedStore_at,inside]
  · rw [relocatedStore_outside address base localStore register (not_exists.mp member)]
    exact (outside register (not_exists.mp member)).symm

theorem relocate_executes_frame {registers targets : Nat} (routine : Routine registers)
    (address : Fin (registers+2) ↪ Fin (targets+2))
    (store target : Fin (targets+2) → List Bool)
    (localInput localOutput : Fin (registers+2) → List Bool) (time : Nat)
    (restricted : store ∘ address = localInput)
    (inside : ∀ source, target (address source) = localOutput source)
    (outside : ∀ register, (∀ source, address source ≠ register) → target register = store register)
    (executed : Executes routine localInput time localOutput) :
    Executes (relocate routine address) store time target := by
  have result := relocate_executes routine address store time localOutput (by
    rw [restricted]
    exact executed)
  rw [relocatedStore_eq address store target localOutput inside outside] at result
  exact result

end Counting.StackMachine.Routine
