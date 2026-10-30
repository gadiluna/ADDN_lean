import Counting.StackNaturalCallMultiply

namespace Counting.StackMachine.NaturalCall
open Routine

theorem callAt_executes {registers : Nat} (routine : Routine 11)
    (roles : Fin 13 ↪ Fin (registers+2)) (store : Fin (registers+2) → List Bool)
    (first second result : List Bool) (time : Nat)
    (restricted : store ∘ roles = file first second [] [] [] [] [])
    (executed : Executes routine (file first second [] [] [] [] []) time
      (file first second result [] [] [] [])) :
    Executes (relocate routine roles) store time (Function.update store (roles 2) result) := by
  have output : file first second result [] [] [] [] =
      Function.update (file first second [] [] [] [] []) 2 result := by
    funext r; fin_cases r <;> rfl
  rw [output,← restricted] at executed
  have relocated := relocate_executes routine roles store time
    (Function.update (store ∘ roles) 2 result) executed
  rw [relocatedStore_update,relocatedStore_original] at relocated
  exact relocated

end Counting.StackMachine.NaturalCall
