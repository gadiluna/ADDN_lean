import Counting.StackRationalNormalize
import Counting.StackNaturalCallRelocate

namespace Counting.StackMachine.RationalArithmetic.Product
open Routine

def file (a b c d sa sc numerator denominator sign common : List Bool) : Fin 20 → List Bool :=
  ![a,b,c,d,sa,sc,numerator,denominator,sign,common,[],[],[],[],[],[],[],[],[],[]]

def numeratorRoles : Fin 13 ↪ Fin 20 := ⟨![0,2,6,10,11,12,13,14,15,16,17,18,19],by decide⟩
def denominatorRoles : Fin 13 ↪ Fin 20 := ⟨![1,3,7,10,11,12,13,14,15,16,17,18,19],by decide⟩
def normalizeRoles : Fin 16 ↪ Fin 20 := ⟨![6,7,9,0,1,8,10,11,12,13,14,15,16,17,18,19],by decide⟩

abbrev numeratorRoutine : Routine 18 := relocate NaturalCall.multiplicationRoutine numeratorRoles
abbrev denominatorRoutine : Routine 18 := relocate NaturalCall.multiplicationRoutine denominatorRoles
abbrev signCase (first : Bool) : Routine 18 := EncodingPrograms.branchRoutine 5
  (pushBit 8 (!first)) (pushBit 8 first)
abbrev signRoutine : Routine 18 := EncodingPrograms.branchRoutine 4 (signCase true) (signCase false)
abbrev prepare : Routine 18 := sequence numeratorRoutine
  (sequence denominatorRoutine (sequence signRoutine (sequence (clear 0) (clear 1))))
abbrev normalized : Routine 18 := relocate normalizationRoutine normalizeRoles
abbrev productRoutine : Routine 18 := sequence prepare normalized

theorem numerator_executes (a b c d sa sc : List Bool) :
    ∃ time ≤ 82000*(a.length+c.length+1)^3,
      Executes numeratorRoutine (file a b c d sa sc [] [] [] []) time
        (file a b c d sa sc (Encoding.value a*Encoding.value c).bits [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.multiplication_executes a c
  have restricted : (file a b c d sa sc [] [] [] []) ∘ numeratorRoles = NaturalCall.file a c [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have called := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine numeratorRoles
    (file a b c d sa sc [] [] [] []) a c _ time restricted ran
  have result : Function.update (file a b c d sa sc [] [] [] []) (numeratorRoles 2)
      (Encoding.value a*Encoding.value c).bits = file a b c d sa sc (Encoding.value a*Encoding.value c).bits [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [result] at called
  exact ⟨time,bounded,called⟩

theorem denominator_executes (a b c d sa sc numerator : List Bool) :
    ∃ time ≤ 82000*(b.length+d.length+1)^3,
      Executes denominatorRoutine (file a b c d sa sc numerator [] [] []) time
        (file a b c d sa sc numerator (Encoding.value b*Encoding.value d).bits [] []) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.multiplication_executes b d
  have restricted : (file a b c d sa sc numerator [] [] []) ∘ denominatorRoles = NaturalCall.file b d [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have called := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine denominatorRoles
    (file a b c d sa sc numerator [] [] []) b d _ time restricted ran
  have result : Function.update (file a b c d sa sc numerator [] [] []) (denominatorRoles 2)
      (Encoding.value b*Encoding.value d).bits = file a b c d sa sc numerator (Encoding.value b*Encoding.value d).bits [] [] := by
    funext r; fin_cases r <;> rfl
  rw [result] at called
  exact ⟨time,bounded,called⟩

theorem sign_executes (a b c d numerator denominator : List Bool) (sa sc : Bool) :
    Executes signRoutine (file a b c d [sa] [sc] numerator denominator [] []) 3
      (file a b c d [] [] numerator denominator [xor sa sc] []) := by
  have emitted (sign : Bool) : Executes (pushBit (registers := 18) 8 sign)
      (file a b c d [] [] numerator denominator [] []) 1
      (file a b c d [] [] numerator denominator [sign] []) := by
    have pushed := pushBit_executes (registers := 18) 8 sign (file a b c d [] [] numerator denominator [] [])
    have result : Function.update (file a b c d [] [] numerator denominator [] []) 8 [sign] =
        file a b c d [] [] numerator denominator [sign] [] := by
      funext r; fin_cases r <;> rfl
    change Executes _ _ 1 (Function.update (file a b c d [] [] numerator denominator [] []) 8 [sign]) at pushed
    rw [result] at pushed
    exact pushed
  have resetSecond : Function.update (file a b c d [] [sc] numerator denominator [] []) 5 [] =
      file a b c d [] [] numerator denominator [] [] := by
    funext r; fin_cases r <;> rfl
  have second := Signed.branch_bit 5 (pushBit 8 (!sa)) (pushBit 8 sa)
    (file a b c d [] [sc] numerator denominator [] []) (file a b c d [] [] numerator denominator [xor sa sc] [])
    sc 1 rfl (by rw [resetSecond]; cases sa <;> cases sc <;> exact emitted _)
  have resetFirst : Function.update (file a b c d [sa] [sc] numerator denominator [] []) 4 [] =
      file a b c d [] [sc] numerator denominator [] [] := by
    funext r; fin_cases r <;> rfl
  exact Signed.branch_bit 4 (signCase true) (signCase false)
    (file a b c d [sa] [sc] numerator denominator [] []) (file a b c d [] [] numerator denominator [xor sa sc] [])
    sa 2 rfl (by rw [resetFirst]; cases sa <;> exact second)

theorem prepare_executes (a b c d : List Bool) (sa sc : Bool) :
    ∃ time ≤ 170000*(a.length+b.length+c.length+d.length+1)^3,
      Executes prepare (file a b c d [sa] [sc] [] [] [] []) time
        (file [] [] c d [] [] (Encoding.value a*Encoding.value c).bits
          (Encoding.value b*Encoding.value d).bits [xor sa sc] []) := by
  let num := (Encoding.value a*Encoding.value c).bits
  let den := (Encoding.value b*Encoding.value d).bits
  obtain ⟨numTime,numBound,numRan⟩ := numerator_executes a b c d [sa] [sc]
  obtain ⟨denTime,denBound,denRan⟩ := denominator_executes a b c d [sa] [sc] num
  have signed := sign_executes a b c d num den sa sc
  have firstCleared := clear_executes (registers := 18) 0 (file a b c d [] [] num den [xor sa sc] [])
  have firstStore : Function.update (file a b c d [] [] num den [xor sa sc] []) 0 [] =
      file [] b c d [] [] num den [xor sa sc] [] := by
    funext r; fin_cases r <;> rfl
  change Executes (clear 0) _ (a.length+1) (Function.update (file a b c d [] [] num den [xor sa sc] []) 0 []) at firstCleared
  rw [firstStore] at firstCleared
  have secondCleared := clear_executes (registers := 18) 1 (file [] b c d [] [] num den [xor sa sc] [])
  have secondStore : Function.update (file [] b c d [] [] num den [xor sa sc] []) 1 [] =
      file [] [] c d [] [] num den [xor sa sc] [] := by
    funext r; fin_cases r <;> rfl
  change Executes (clear 1) _ (b.length+1) (Function.update (file [] b c d [] [] num den [xor sa sc] []) 1 []) at secondCleared
  rw [secondStore] at secondCleared
  refine ⟨_,?_,numRan.sequence (denRan.sequence (signed.sequence (firstCleared.sequence secondCleared)))⟩
  have np := Nat.pow_le_pow_left (show a.length+c.length+1 ≤ a.length+b.length+c.length+d.length+1 by omega) 3
  have dp := Nat.pow_le_pow_left (show b.length+d.length+1 ≤ a.length+b.length+c.length+d.length+1 by omega) 3
  have linear : a.length+b.length+c.length+d.length+1 ≤ (a.length+b.length+c.length+d.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (a.length+b.length+c.length+d.length)
    have product := Nat.mul_le_mul_left (a.length+b.length+c.length+d.length+1) square
    nlinarith
  omega

end Counting.StackMachine.RationalArithmetic.Product
