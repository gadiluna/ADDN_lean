import Counting.StackRoutineSemantics
import Counting.StackListPrograms

namespace Counting.StackMachine.Routine

/-- Reuse the exact copy routine through the compositional store interface.
Only the destination changes; the scratch emptiness precondition is explicit. -/
theorem copy_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (store : Fin (extra+3) → List Bool) (work : store temporary = []) :
    Executes (ofProgram (ListPrograms.copyProgram extra source target temporary)) store
      (5*(store source).length+2) (Function.update store target (store source++store target)) := by
  have start : ListPrograms.copyConfig extra source target temporary 0 store (store source) (store target) [] =
      (⟨0,store⟩ : Config (ListPrograms.copyProgram extra source target temporary)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register = source
    · subst register; simp
    · by_cases b : register = target
      · subst register; simp [a]
      · by_cases c : register = temporary
        · subst register; simp [a,b,work]
        · simp [a,b,c]
  refine ⟨ListPrograms.copyConfig extra source target temporary 8 store (store source) (store source++store target) [],
    ?_,ListPrograms.copy_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact ListPrograms.copy_run extra source target temporary st sw tw store (store source) (store target)
  · funext register
    dsimp only [ListPrograms.copyConfig]
    split_ifs <;> simp_all [Function.update]
    intro equal
    exact False.elim (st equal)

/-- Destructive reversal also preserves every register outside its two operands. -/
theorem reverse_executes (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (store : Fin (extra+2) → List Bool) :
    Executes (ofProgram (ListPrograms.reverseProgram extra source target)) store
      (2*(store source).length+1)
      (Function.update (Function.update store source []) target ((store source).reverse++store target)) := by
  have start : ListPrograms.reverseConfig extra source target 0 store (store source) (store target) =
      (⟨0,store⟩ : Config (ListPrograms.reverseProgram extra source target)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register = source
    · subst register; simp
    · by_cases b : register = target
      · subst register; simp [a]
      · simp [a,b]
  refine ⟨ListPrograms.reverseConfig extra source target 3 store [] ((store source).reverse++store target),
    ?_,ListPrograms.reverse_halted _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact ListPrograms.reverse_run extra source target distinct store (store source) (store target)
  · funext register
    dsimp only [ListPrograms.reverseConfig]
    split_ifs <;> simp_all [Function.update]
    intro equal
    exact False.elim (distinct equal)

end Counting.StackMachine.Routine
