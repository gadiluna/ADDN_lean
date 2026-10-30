import Counting.StackBinarySubtract
import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine
open Binary

/-- Generic arithmetic with a complete register-file contract. -/
theorem binary_subtract_executes (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (store : Fin (extra+3) → List Bool) :
    Executes (ofProgram (Binary.subtractProgram extra first second output)) store (3*max (store first).length (store second).length+2)
        (Function.update (Function.update (Function.update store first []) second []) output
          ((subtractBits false (store first) (store second)).1.reverse++store output)) := by
  have start : Binary.subtractConfig extra first second output 0 store (store first) (store second) (store output) =
      (⟨0,store⟩ : Config (Binary.subtractProgram extra first second output)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register=first
    · subst register; simp
    · by_cases b : register=second
      · subst register; simp [a]
      · by_cases c : register=output
        · subst register; simp [a,b]
        · simp [a,b,c]
  have executed := Binary.subtract_run extra first second output fs fo so store false
    (store first) (store second) (store output)
  refine ⟨Binary.subtractConfig extra first second output (Binary.subtractEnd extra first second output (subtractBits false (store first) (store second)).2) store [] []
      ((subtractBits false (store first) (store second)).1.reverse++store output),?_,
    Binary.subtract_halted _ _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact executed
  · funext register
    dsimp only [Binary.subtractConfig]
    by_cases a : register=first
    · subst register
      simp [Function.update]
      intro equal
      exact False.elim (fo equal)
    · by_cases b : register=second
      · subst register
        simp [Function.update,a]
        intro equal
        exact False.elim (so equal)
      · by_cases c : register=output
        · subst register; simp [Function.update,a,b]
        · simp [Function.update,a,b,c]

end Counting.StackMachine.Routine
