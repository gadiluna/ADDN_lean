import Counting.StackRationalProductCorrectness

namespace Counting.StackMachine.RationalArithmetic.Addition
open Routine

def file (a b c d sa sc left right denominator numerator sign common : List Bool) : Fin 22 → List Bool :=
  ![a,b,c,d,sa,sc,left,right,denominator,numerator,sign,common,[],[],[],[],[],[],[],[],[],[]]

def leftRoles : Fin 13 ↪ Fin 22 := ⟨![0,3,6,12,13,14,15,16,17,18,19,20,21],by decide⟩
def rightRoles : Fin 13 ↪ Fin 22 := ⟨![2,1,7,12,13,14,15,16,17,18,19,20,21],by decide⟩
def denominatorRoles : Fin 13 ↪ Fin 22 := ⟨![1,3,8,12,13,14,15,16,17,18,19,20,21],by decide⟩

abbrev leftRoutine : Routine 20 := relocate NaturalCall.multiplicationRoutine leftRoles
abbrev rightRoutine : Routine 20 := relocate NaturalCall.multiplicationRoutine rightRoles
abbrev denominatorRoutine : Routine 20 := relocate NaturalCall.multiplicationRoutine denominatorRoles
abbrev products : Routine 20 := sequence leftRoutine (sequence rightRoutine denominatorRoutine)

theorem left_executes (a b c d sa sc : List Bool) :
    ∃ time ≤ 82000*(a.length+d.length+1)^3,
      Executes leftRoutine (file a b c d sa sc [] [] [] [] [] []) time
        (file a b c d sa sc (Encoding.value a*Encoding.value d).bits [] [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.multiplication_executes a d
  have restricted : (file a b c d sa sc [] [] [] [] [] []) ∘ leftRoles = NaturalCall.file a d [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have called := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine leftRoles
    (file a b c d sa sc [] [] [] [] [] []) a d _ time restricted ran
  have result : Function.update (file a b c d sa sc [] [] [] [] [] []) (leftRoles 2)
      (Encoding.value a*Encoding.value d).bits = file a b c d sa sc (Encoding.value a*Encoding.value d).bits [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [result] at called
  exact ⟨time,bounded,called⟩

theorem right_executes (a b c d sa sc left : List Bool) :
    ∃ time ≤ 82000*(c.length+b.length+1)^3,
      Executes rightRoutine (file a b c d sa sc left [] [] [] [] []) time
        (file a b c d sa sc left (Encoding.value c*Encoding.value b).bits [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.multiplication_executes c b
  have restricted : (file a b c d sa sc left [] [] [] [] []) ∘ rightRoles = NaturalCall.file c b [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have called := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine rightRoles
    (file a b c d sa sc left [] [] [] [] []) c b _ time restricted ran
  have result : Function.update (file a b c d sa sc left [] [] [] [] []) (rightRoles 2)
      (Encoding.value c*Encoding.value b).bits = file a b c d sa sc left (Encoding.value c*Encoding.value b).bits [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [result] at called
  exact ⟨time,bounded,called⟩

theorem denominator_executes (a b c d sa sc left right : List Bool) :
    ∃ time ≤ 82000*(b.length+d.length+1)^3,
      Executes denominatorRoutine (file a b c d sa sc left right [] [] [] []) time
        (file a b c d sa sc left right (Encoding.value b*Encoding.value d).bits [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.multiplication_executes b d
  have restricted : (file a b c d sa sc left right [] [] [] []) ∘ denominatorRoles = NaturalCall.file b d [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have called := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine denominatorRoles
    (file a b c d sa sc left right [] [] [] []) b d _ time restricted ran
  have result : Function.update (file a b c d sa sc left right [] [] [] []) (denominatorRoles 2)
      (Encoding.value b*Encoding.value d).bits = file a b c d sa sc left right (Encoding.value b*Encoding.value d).bits [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [result] at called
  exact ⟨time,bounded,called⟩

theorem products_executes (a b c d sa sc : List Bool) :
    ∃ time ≤ 250000*(a.length+b.length+c.length+d.length+1)^3,
      Executes products (file a b c d sa sc [] [] [] [] [] []) time
        (file a b c d sa sc (Encoding.value a*Encoding.value d).bits
          (Encoding.value c*Encoding.value b).bits (Encoding.value b*Encoding.value d).bits [] [] []) := by
  obtain ⟨leftTime,leftBound,leftRan⟩ := left_executes a b c d sa sc
  obtain ⟨rightTime,rightBound,rightRan⟩ := right_executes a b c d sa sc (Encoding.value a*Encoding.value d).bits
  obtain ⟨denTime,denBound,denRan⟩ := denominator_executes a b c d sa sc
    (Encoding.value a*Encoding.value d).bits (Encoding.value c*Encoding.value b).bits
  refine ⟨_,?_,leftRan.sequence (rightRan.sequence denRan)⟩
  have p := Nat.pow_le_pow_left (show a.length+d.length+1 ≤ a.length+b.length+c.length+d.length+1 by omega) 3
  have q := Nat.pow_le_pow_left (show c.length+b.length+1 ≤ a.length+b.length+c.length+d.length+1 by omega) 3
  have r := Nat.pow_le_pow_left (show b.length+d.length+1 ≤ a.length+b.length+c.length+d.length+1 by omega) 3
  have positive := Nat.one_le_pow' 3 (a.length+b.length+c.length+d.length)
  omega

end Counting.StackMachine.RationalArithmetic.Addition
