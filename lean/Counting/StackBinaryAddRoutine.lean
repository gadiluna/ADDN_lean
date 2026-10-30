import Counting.StackBinaryAdd
import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine
open Arithmetic

/-- Generic arithmetic with a complete register-file contract. -/
theorem binary_add_executes (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (store : Fin (extra+3) → List Bool) :
    ∃ transitions ≤ 3*((store first).length+(store second).length)+3,
      Executes (ofProgram (Binary.addProgram extra first second output)) store transitions
        (Function.update (Function.update (Function.update store first []) second []) output
          ((addBits false (store first) (store second)).reverse++store output)) := by
  have start : Binary.addConfig extra first second output 0 store (store first) (store second) (store output) =
      (⟨0,store⟩ : Config (Binary.addProgram extra first second output)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register=first
    · subst register; simp
    · by_cases b : register=second
      · subst register; simp [a]
      · by_cases c : register=output
        · subst register; simp [a,b]
        · simp [a,b,c]
  obtain ⟨transitions,bounded,executed⟩ := Binary.add_run extra first second output fs fo so store false
    (store first) (store second) (store output)
  refine ⟨transitions,bounded,
    Binary.addConfig extra first second output 13 store [] []
      ((addBits false (store first) (store second)).reverse++store output),?_,
    Binary.add_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact executed
  · funext register
    dsimp only [Binary.addConfig]
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
