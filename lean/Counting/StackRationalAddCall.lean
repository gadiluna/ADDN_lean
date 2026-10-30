import Counting.StackRationalAddComplete
import Counting.StackRoutineClean

namespace Counting.StackMachine.RationalAddCall
open Routine

/-- Three public registers, one scratch register, and the twenty-two-register
private bank of the actual rational addition transducer. -/
def file (first second output input encoded : List Bool) : Fin 26 → List Bool :=
  ![first,second,output,[],input,encoded,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def addresses : Fin 22 ↪ Fin 26 := ⟨fun r => ⟨r.val+4,by omega⟩,
  by intro a b equal; apply Fin.ext; have := congrArg (fun r : Fin 26 => r.val) equal; dsimp at this; omega⟩
abbrev prepare : Routine 24 := sequence
  (ofProgram (ListPrograms.copyProgram 23 1 4 3))
  (ofProgram (ListPrograms.copyProgram 23 0 4 3))
abbrev addition : Routine 24 := sequence prepare
  (sequence (relocate (isolate RationalArithmetic.Addition.completeAddition) addresses) (move 23 5 2 3))

theorem prepare_executes (first second : List Bool) :
    Executes prepare (file first second [] [] []) (5*second.length+2+1+(5*first.length+2))
      (file first second [] (first++second) []) := by
  have secondRan := copy_executes 23 1 4 3 (by decide) (by decide) (by decide) (file first second [] [] []) rfl
  have secondStore : Function.update (file first second [] [] []) 4 (second++[]) = file first second [] second [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*second.length+2) (Function.update (file first second [] [] []) 4 (second++[])) at secondRan
  rw [secondStore] at secondRan
  have firstRan := copy_executes 23 0 4 3 (by decide) (by decide) (by decide) (file first second [] second []) rfl
  have firstStore : Function.update (file first second [] second []) 4 (first++second) = file first second [] (first++second) [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*first.length+2) (Function.update (file first second [] second []) 4 (first++second)) at firstRan
  rw [firstStore] at firstRan
  exact secondRan.sequence firstRan

theorem addition_executes (first second : List Bool) :
    ∃ time ≤ 500000000*(first.length+second.length+1)^3,
      Executes addition (file first second [] [] []) time
        (file first second (RationalArithmetic.Addition.additionFunction (first++second)) [] []) := by
  let input := first++second
  let value := RationalArithmetic.Addition.additionFunction input
  have prepared := prepare_executes first second
  obtain ⟨time,bounded,ran⟩ := isolate_executes RationalArithmetic.Addition.completeAddition
    RationalArithmetic.Addition.additionFunction (Complexity.polynomial 14000000 3)
    RationalArithmetic.Addition.addition_computes input
  have restricted : (file first second [] input []) ∘ addresses = inputStore 20 input := by
    funext r; fin_cases r <;> simp [file,addresses,inputStore]
  have called : Executes (relocate (isolate RationalArithmetic.Addition.completeAddition) addresses)
      (file first second [] input []) time (file first second [] [] value) := by
    apply relocate_executes_frame (isolate RationalArithmetic.Addition.completeAddition) addresses _ _ _ _ time restricted _ _ ran
    · intro r; fin_cases r <;> simp [file,addresses,outputStore,value]
    · intro r outside
      fin_cases r
      · simp [file]
      · simp [file]
      · simp [file]
      · simp [file]
      · exact False.elim (outside 0 rfl)
      · exact False.elim (outside 1 rfl)
      all_goals simp [file]
  have moved := move_executes 23 5 2 3 (by decide) (by decide) (by decide) (file first second [] [] value) rfl
  have movedStore : Function.update (Function.update (file first second [] [] value) 2 (value++[])) 5 [] =
      file first second value [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*value.length+4)
    (Function.update (Function.update (file first second [] [] value) 2 (value++[])) 5 []) at moved
  rw [movedStore] at moved
  refine ⟨_,?_,prepared.sequence (called.sequence moved)⟩
  have resultBound := computed_length_le RationalArithmetic.Addition.completeAddition
    RationalArithmetic.Addition.additionFunction (Complexity.polynomial 14000000 3)
    RationalArithmetic.Addition.addition_computes input
  change value.length ≤ input.length+14000000*(input.length+1)^3 at resultBound
  change time ≤ 23*(14000000*(input.length+1)^3+input.length+3) at bounded
  have inputLen : input.length=first.length+second.length := List.length_append
  rw [inputLen] at bounded resultBound
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (first.length+second.length)
    have product := Nat.mul_le_mul_left (first.length+second.length+1) square
    nlinarith
  omega

/-- Both encoded operands are preserved, every private register is empty,
and the returned value uses the canonical rational codec. -/
theorem addition_rationals (first second : Rat) :
    ∃ time ≤ 500000000*((Encoding.rational.encode first).length+(Encoding.rational.encode second).length+1)^3,
      Executes addition (file (Encoding.rational.encode first) (Encoding.rational.encode second) [] [] []) time
        (file (Encoding.rational.encode first) (Encoding.rational.encode second) (Encoding.rational.encode (first+second)) [] []) := by
  obtain ⟨time,bounded,ran⟩ := addition_executes (Encoding.rational.encode first) (Encoding.rational.encode second)
  have same := RationalArithmetic.Addition.additionFunction_rationals first second
  change RationalArithmetic.Addition.additionFunction (Encoding.rational.encode first++Encoding.rational.encode second) = _ at same
  rw [same] at ran
  exact ⟨time,bounded,ran⟩

end Counting.StackMachine.RationalAddCall
