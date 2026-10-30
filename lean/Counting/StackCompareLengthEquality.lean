import Counting.StackCompare
import Counting.StackRoutineUnary

/-! Equality with a unary length counter and preserved operands and reusable empty scratch registers. -/
namespace Counting.StackMachine.Compare

/-- Roles 0/1 are operands, 2 is Boolean output, and 3/4/5 are empty
scratch registers. The embedding permits use inside larger programs. -/
def preservingLengthEquality (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4) :=
  Routine.sequence
    (Routine.ofProgram (Unary.lengthProgram (extra+3) (roles 0) (roles 3) (roles 5)))
    (Routine.sequence
      (Routine.ofProgram (ListPrograms.copyProgram (extra+3) (roles 1) (roles 4) (roles 5)))
      (Routine.ofProgram (equalityProgram (extra+4) (roles 3) (roles 4) (roles 2))))

def preservingLengthEqualityCost (a b : List Bool) : Nat := 5*a.length+2+1+(5*b.length+2+1+equalityCost (List.replicate a.length true) b)

theorem preservingLengthEqualityCost_le (a b : List Bool) :
    preservingLengthEqualityCost a b ≤ 6*(a.length+b.length)+11 := by
  have bounded := equalityCost_le (List.replicate a.length true) b
  simp only [List.length_replicate] at bounded
  dsimp only [preservingLengthEqualityCost]
  omega

/-- The entire final store agrees with its initial value except that the
answer is prepended to output. Both original strings and all scratch are preserved. -/
theorem preservingLengthEquality_executes (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6))
    (store : Fin (extra+6) → List Bool)
    (leftEmpty : store (roles 3) = []) (rightEmpty : store (roles 4) = [])
    (workEmpty : store (roles 5) = [])
    (unary : store (roles 1)=List.replicate (store (roles 1)).length true) :
    Routine.Executes (preservingLengthEquality extra roles) store
      (preservingLengthEqualityCost (store (roles 0)) (store (roles 1)))
      (Function.update store (roles 2) (decide ((store (roles 0)).length=(store (roles 1)).length)::store (roles 2))) := by
  have distinct (i j : Fin 6) (h : i ≠ j) : roles i ≠ roles j :=
    fun equal => h (roles.injective equal)
  let first := Function.update store (roles 3) (List.replicate (store (roles 0)).length true)
  let second := Function.update first (roles 4) (store (roles 1))
  have copiedLeft : Routine.Executes
      (Routine.ofProgram (Unary.lengthProgram (extra+3) (roles 0) (roles 3) (roles 5)))
      store (5*(store (roles 0)).length+2) first := by
    simpa +instances only [Unary.lengthProgram,first,leftEmpty,List.append_nil] using
      Routine.length_executes (extra+3) (roles 0) (roles 3) (roles 5)
        (distinct 0 3 (by decide)) (distinct 0 5 (by decide)) (distinct 3 5 (by decide)) store workEmpty
  have firstAt (i : Fin 6) (h : i ≠ 3) : first (roles i) = store (roles i) := by
    simp only [first,Function.update_of_ne (distinct i 3 h)]
  have copiedRight : Routine.Executes
      (Routine.ofProgram (ListPrograms.copyProgram (extra+3) (roles 1) (roles 4) (roles 5)))
      first (5*(store (roles 1)).length+2) second := by
    have run := Routine.copy_executes (extra+3) (roles 1) (roles 4) (roles 5)
      (distinct 1 4 (by decide)) (distinct 1 5 (by decide)) (distinct 4 5 (by decide)) first
      (by rw [firstAt 5 (by decide),workEmpty])
    simpa +instances only [ListPrograms.copyProgram,firstAt 1 (by decide),firstAt 4 (by decide),rightEmpty,List.append_nil,second] using run
  have secondLeft : second (roles 3) = List.replicate (store (roles 0)).length true := by
    simp only [second,Function.update_of_ne (distinct 3 4 (by decide)),first,Function.update_self]
  have secondRight : second (roles 4) = store (roles 1) := by simp only [second,Function.update_self]
  have secondOutput : second (roles 2) = store (roles 2) := by
    simp only [second,Function.update_of_ne (distinct 2 4 (by decide)),firstAt 2 (by decide)]
  have compared := equality_executes (extra+4) (roles 3) (roles 4) (roles 2)
    (distinct 3 4 (by decide)) (distinct 3 2 (by decide)) (distinct 4 2 (by decide)) second
  simp +instances only [equalityProgram] at compared
  rw [secondLeft,secondRight,secondOutput] at compared
  have restored : Function.update (Function.update second (roles 3) []) (roles 4) [] = store := by
    funext r
    by_cases a : r=roles 3
    · subst r
      simp only [Function.update_of_ne (distinct 3 4 (by decide)),Function.update_self,leftEmpty]
    · by_cases b : r=roles 4
      · subst r; simp only [Function.update_self,rightEmpty]
      · simp only [Function.update_of_ne b,Function.update_of_ne a,second,first]
  rw [restored] at compared
  have same : List.replicate (store (roles 0)).length true=store (roles 1) ↔
      (store (roles 0)).length=(store (roles 1)).length := by
    constructor
    · intro equal
      simpa only [List.length_replicate] using congrArg List.length equal
    · intro equal
      rw [equal,←unary]
  have flag : decide (List.replicate (store (roles 0)).length true=store (roles 1)) =
      decide ((store (roles 0)).length=(store (roles 1)).length) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using same
  rw [flag] at compared
  exact copiedLeft.sequence (copiedRight.sequence compared)

end Counting.StackMachine.Compare
