import Counting.StackRoutineSemantics
import Counting.StackUnaryBinary

namespace Counting.StackMachine.Routine

/-- Reuse the exact copy routine through the compositional store interface.
Only the destination changes; the scratch emptiness precondition is explicit. -/
theorem length_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (store : Fin (extra+3) → List Bool) (work : store temporary = []) :
    Executes (ofProgram (Unary.lengthProgram extra source target temporary)) store
      (5*(store source).length+2) (Function.update store target (List.replicate (store source).length true++store target)) := by
  have start : Unary.lengthConfig extra source target temporary 0 store (store source) (store target) [] =
      (⟨0,store⟩ : Config (Unary.lengthProgram extra source target temporary)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register = source
    · subst register; simp
    · by_cases b : register = target
      · subst register; simp [a]
      · by_cases c : register = temporary
        · subst register; simp [a,b,work]
        · simp [a,b,c]
  refine ⟨Unary.lengthConfig extra source target temporary 8 store (store source) (List.replicate (store source).length true++store target) [],
    ?_,Unary.length_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact Unary.length_run extra source target temporary st sw tw store (store source) (store target)
  · funext register
    dsimp only [Unary.lengthConfig]
    split_ifs <;> simp_all [Function.update]
    intro equal
    exact False.elim (st equal)


/-- Convert a consumed unary counter into a canonical accumulator, with
scratch emptiness and all unchanged registers explicit. -/
theorem toBinary_executes (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter ≠ accumulator) (cs : counter ≠ scratch) (as : accumulator ≠ scratch)
    (store : Fin (extra+3) → List Bool) (initial : Nat)
    (binary : store accumulator = initial.bits) (work : store scratch = []) :
    ∃ transitions ≤ 4*(store counter).length*(initial+(store counter).length+1)+1,
      Executes (ofProgram (Unary.toBinaryProgram extra counter accumulator scratch)) store transitions
        (Function.update (Function.update store counter []) accumulator
          (initial+(store counter).length).bits) := by
  have start : Unary.binaryConfig extra counter accumulator scratch 0 store (store counter) initial.bits [] =
      (⟨0,store⟩ : Config (Unary.toBinaryProgram extra counter accumulator scratch)) := by
    apply congrArg (Config.mk _)
    funext register
    by_cases a : register=counter
    · subst register; simp
    · by_cases b : register=accumulator
      · subst register; simp [a,binary]
      · by_cases c : register=scratch
        · subst register; simp [a,b,work]
        · simp [a,b,c]
  obtain ⟨transitions,bounded,executed⟩ := Unary.toBinary_run extra counter accumulator scratch ca cs as
    store (store counter) initial
  refine ⟨transitions,bounded,Unary.binaryConfig extra counter accumulator scratch 6 store []
    (initial+(store counter).length).bits [],?_,Unary.toBinary_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact executed
  · funext register
    dsimp only [Unary.binaryConfig]
    split_ifs <;> simp_all [Function.update]
    intro equal
    exact False.elim (ca equal)

end Counting.StackMachine.Routine
