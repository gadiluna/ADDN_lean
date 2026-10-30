import Counting.StackRationalProductComplete
import Counting.StackRoutineClean

namespace Counting.StackMachine.RationalCall
open Routine

/-- Three public registers, one scratch register, and the twenty-register
private bank of the actual rational multiplication transducer. -/
def file (first second output input encoded : List Bool) : Fin 24 → List Bool :=
  ![first,second,output,[],input,encoded,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def addresses : Fin 20 ↪ Fin 24 := ⟨fun r => ⟨r.val+4,by omega⟩,
  by intro a b equal; apply Fin.ext; have := congrArg (fun r : Fin 24 => r.val) equal; dsimp at this; omega⟩
abbrev prepare : Routine 22 := sequence
  (ofProgram (ListPrograms.copyProgram 21 1 4 3))
  (ofProgram (ListPrograms.copyProgram 21 0 4 3))
abbrev multiplication : Routine 22 := sequence prepare
  (sequence (relocate (isolate RationalArithmetic.Product.completeProduct) addresses) (move 21 5 2 3))

theorem prepare_executes (first second : List Bool) :
    Executes prepare (file first second [] [] []) (5*second.length+2+1+(5*first.length+2))
      (file first second [] (first++second) []) := by
  have secondRan := copy_executes 21 1 4 3 (by decide) (by decide) (by decide) (file first second [] [] []) rfl
  have secondStore : Function.update (file first second [] [] []) 4 (second++[]) = file first second [] second [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*second.length+2) (Function.update (file first second [] [] []) 4 (second++[])) at secondRan
  rw [secondStore] at secondRan
  have firstRan := copy_executes 21 0 4 3 (by decide) (by decide) (by decide) (file first second [] second []) rfl
  have firstStore : Function.update (file first second [] second []) 4 (first++second) = file first second [] (first++second) [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*first.length+2) (Function.update (file first second [] second []) 4 (first++second)) at firstRan
  rw [firstStore] at firstRan
  exact secondRan.sequence firstRan

theorem multiplication_executes (first second : List Bool) :
    ∃ time ≤ 90000000*(first.length+second.length+1)^3,
      Executes multiplication (file first second [] [] []) time
        (file first second (RationalArithmetic.Product.productFunction (first++second)) [] []) := by
  let input := first++second
  let value := RationalArithmetic.Product.productFunction input
  have prepared := prepare_executes first second
  obtain ⟨time,bounded,ran⟩ := isolate_executes RationalArithmetic.Product.completeProduct
    RationalArithmetic.Product.productFunction (Complexity.polynomial 3000000 3)
    RationalArithmetic.Product.product_computes input
  have restricted : (file first second [] input []) ∘ addresses = inputStore 18 input := by
    funext r; fin_cases r <;> simp [file,addresses,inputStore]
  have called : Executes (relocate (isolate RationalArithmetic.Product.completeProduct) addresses)
      (file first second [] input []) time (file first second [] [] value) := by
    apply relocate_executes_frame (isolate RationalArithmetic.Product.completeProduct) addresses _ _ _ _ time restricted _ _ ran
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
  have moved := move_executes 21 5 2 3 (by decide) (by decide) (by decide) (file first second [] [] value) rfl
  have movedStore : Function.update (Function.update (file first second [] [] value) 2 (value++[])) 5 [] =
      file first second value [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*value.length+4)
    (Function.update (Function.update (file first second [] [] value) 2 (value++[])) 5 []) at moved
  rw [movedStore] at moved
  refine ⟨_,?_,prepared.sequence (called.sequence moved)⟩
  have resultBound := computed_length_le RationalArithmetic.Product.completeProduct
    RationalArithmetic.Product.productFunction (Complexity.polynomial 3000000 3)
    RationalArithmetic.Product.product_computes input
  change value.length ≤ input.length+3000000*(input.length+1)^3 at resultBound
  change time ≤ 21*(3000000*(input.length+1)^3+input.length+3) at bounded
  have inputLen : input.length=first.length+second.length := List.length_append
  rw [inputLen] at bounded resultBound
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (first.length+second.length)
    have product := Nat.mul_le_mul_left (first.length+second.length+1) square
    nlinarith
  omega

/-- Both encoded operands are preserved, every private register is empty,
and the returned value uses the canonical rational codec. -/
theorem multiplication_rationals (first second : Rat) :
    ∃ time ≤ 90000000*((Encoding.rational.encode first).length+(Encoding.rational.encode second).length+1)^3,
      Executes multiplication (file (Encoding.rational.encode first) (Encoding.rational.encode second) [] [] []) time
        (file (Encoding.rational.encode first) (Encoding.rational.encode second) (Encoding.rational.encode (first*second)) [] []) := by
  obtain ⟨time,bounded,ran⟩ := multiplication_executes (Encoding.rational.encode first) (Encoding.rational.encode second)
  have same := RationalArithmetic.Product.productFunction_rationals first second
  change RationalArithmetic.Product.productFunction (Encoding.rational.encode first++Encoding.rational.encode second) = _ at same
  rw [same] at ran
  exact ⟨time,bounded,ran⟩

end Counting.StackMachine.RationalCall
