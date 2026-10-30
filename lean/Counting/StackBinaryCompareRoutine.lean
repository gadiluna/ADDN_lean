import Counting.StackBinaryCompare
import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine
open Binary

/-- Generic arithmetic with a complete register-file contract. -/
theorem binary_compare_executes (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (store : Fin (extra+3) → List Bool) :
    Executes (ofProgram (Binary.compareProgram extra first second output)) store (2*max (store first).length (store second).length+3)
        (Function.update (Function.update (Function.update store first []) second []) output
          (compareBits true (store first) (store second)::store output)) := by
  have start : Binary.compareConfig extra first second output 0 store (store first) (store second) (store output) =
      (⟨0,store⟩ : Config (Binary.compareProgram extra first second output)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register=first
    · subst register; simp
    · by_cases b : register=second
      · subst register; simp [a]
      · by_cases c : register=output
        · subst register; simp [a,b]
        · simp [a,b,c]
  have executed := Binary.compare_run extra first second output fs fo so store true
    (store first) (store second) (store output)
  refine ⟨Binary.compareConfig extra first second output 10 store [] []
      (compareBits true (store first) (store second)::store output),?_,
    Binary.compare_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact executed
  · funext register
    dsimp only [Binary.compareConfig]
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
