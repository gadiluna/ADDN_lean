import Counting.StackRegisterFrames

/-! Parser-facing register-embedding interface. The generated code and
exact simulation reuse the project's existing `Routine.relocate`; there is
no second compiler or uncosted store permutation. -/
namespace Counting.StackMachine.Routine

abbrev mapRegisters {source target : Nat} (roles : Fin (source+2) ↪ Fin (target+2))
    (routine : Routine source) : Routine target := relocate routine roles

theorem mapRegisters_executes {source target : Nat} (roles : Fin (source+2) ↪ Fin (target+2))
    (routine : Routine source) (store : Store target) (time : Nat) (result : Store source)
    (executed : Executes routine (fun r=>store (roles r)) time result) :
    ∃ output : Store target, Executes (mapRegisters roles routine) store time output ∧
      (∀ r,output (roles r)=result r) ∧
      (∀ r,(∀ i,roles i≠r) → output r=store r) := by
  refine ⟨relocatedStore roles store result,relocate_executes routine roles store time result executed,?_,?_⟩
  · intro r; exact relocatedStore_at roles store result r
  · intro r outside; exact relocatedStore_outside roles store result r outside

end Counting.StackMachine.Routine
