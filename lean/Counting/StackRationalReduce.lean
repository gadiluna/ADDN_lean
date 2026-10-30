import Counting.StackNaturalCallArithmetic
import Counting.RationalBinarySpecification

namespace Counting.StackMachine.RationalArithmetic
open Routine Binary

def file (numerator denominator common reducedNum reducedDen sign : List Bool) : Fin 16 → List Bool :=
  ![numerator,denominator,common,reducedNum,reducedDen,sign,[],[],[],[],[],[],[],[],[],[]]

def gcdRoles : Fin 13 ↪ Fin 16 := ⟨![0,1,2,6,7,8,9,10,11,12,13,14,15],by decide⟩
def numeratorRoles : Fin 13 ↪ Fin 16 := ⟨![0,2,3,6,7,8,9,10,11,12,13,14,15],by decide⟩
def denominatorRoles : Fin 13 ↪ Fin 16 := ⟨![1,2,4,6,7,8,9,10,11,12,13,14,15],by decide⟩

abbrev computeGcd : Routine 14 := relocate NaturalCall.gcdRoutine gcdRoles
abbrev divideNumerator : Routine 14 := relocate NaturalCall.divisionRoutine numeratorRoles
abbrev divideDenominator : Routine 14 := relocate NaturalCall.divisionRoutine denominatorRoles
abbrev divisions : Routine 14 := sequence computeGcd (sequence divideNumerator divideDenominator)

theorem callAt_executes (routine : Routine 11) (roles : Fin 13 ↪ Fin 16)
    (store : Fin 16 → List Bool) (first second result : List Bool) (time : Nat)
    (restricted : store ∘ roles = NaturalCall.file first second [] [] [] [] [])
    (executed : Executes routine (NaturalCall.file first second [] [] [] [] []) time
      (NaturalCall.file first second result [] [] [] [])) :
    Executes (relocate routine roles) store time (Function.update store (roles 2) result) := by
  have output : NaturalCall.file first second result [] [] [] [] =
      Function.update (NaturalCall.file first second [] [] [] [] []) 2 result := by
    funext r; fin_cases r <;> rfl
  rw [output,← restricted] at executed
  have relocated := relocate_executes routine roles store time
    (Function.update (store ∘ roles) 2 result) executed
  rw [relocatedStore_update,relocatedStore_original] at relocated
  exact relocated

theorem gcd_executes (numerator denominator sign : List Bool) :
    ∃ time ≤ 820000*(numerator.length+denominator.length+1)^3,
      Executes computeGcd (file numerator denominator [] [] [] sign) time
        (file numerator denominator (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits [] [] sign) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.gcd_executes numerator denominator
  have restricted : (file numerator denominator [] [] [] sign) ∘ gcdRoles =
      NaturalCall.file numerator denominator [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have lifted := callAt_executes NaturalCall.gcdRoutine gcdRoles (file numerator denominator [] [] [] sign)
    numerator denominator _ time restricted ran
  have result : Function.update (file numerator denominator [] [] [] sign) (gcdRoles 2)
      (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits =
      file numerator denominator (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits [] [] sign := by
    funext r; fin_cases r <;> rfl
  rw [result] at lifted
  exact ⟨time,bounded,lifted⟩

theorem numerator_executes (numerator denominator common sign : List Bool) :
    ∃ time ≤ 50000*(numerator.length+common.length+1)^2,
      Executes divideNumerator (file numerator denominator common [] [] sign) time
        (file numerator denominator common (Encoding.value numerator/Encoding.value common).bits [] sign) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.division_executes numerator common
  have restricted : (file numerator denominator common [] [] sign) ∘ numeratorRoles =
      NaturalCall.file numerator common [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have lifted := callAt_executes NaturalCall.divisionRoutine numeratorRoles (file numerator denominator common [] [] sign)
    numerator common _ time restricted ran
  have result : Function.update (file numerator denominator common [] [] sign) (numeratorRoles 2)
      (Encoding.value numerator/Encoding.value common).bits =
      file numerator denominator common (Encoding.value numerator/Encoding.value common).bits [] sign := by
    funext r; fin_cases r <;> rfl
  rw [result] at lifted
  exact ⟨time,bounded,lifted⟩

theorem denominator_executes (numerator denominator common reduced sign : List Bool) :
    ∃ time ≤ 50000*(denominator.length+common.length+1)^2,
      Executes divideDenominator (file numerator denominator common reduced [] sign) time
        (file numerator denominator common reduced (Encoding.value denominator/Encoding.value common).bits sign) := by
  obtain ⟨time,bounded,ran⟩ := NaturalCall.division_executes denominator common
  have restricted : (file numerator denominator common reduced [] sign) ∘ denominatorRoles =
      NaturalCall.file denominator common [] [] [] [] [] := by
    funext r; fin_cases r <;> rfl
  have lifted := callAt_executes NaturalCall.divisionRoutine denominatorRoles (file numerator denominator common reduced [] sign)
    denominator common _ time restricted ran
  have result : Function.update (file numerator denominator common reduced [] sign) (denominatorRoles 2)
      (Encoding.value denominator/Encoding.value common).bits =
      file numerator denominator common reduced (Encoding.value denominator/Encoding.value common).bits sign := by
    funext r; fin_cases r <;> rfl
  rw [result] at lifted
  exact ⟨time,bounded,lifted⟩

theorem divisions_executes (numerator denominator sign : List Bool) :
    ∃ time ≤ 1300000*(numerator.length+denominator.length+1)^3,
      Executes divisions (file numerator denominator [] [] [] sign) time
        (file numerator denominator (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits
          (Encoding.value numerator/Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits
          (Encoding.value denominator/Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits sign) := by
  let common := Nat.gcd (Encoding.value numerator) (Encoding.value denominator)
  obtain ⟨gcdTime,gcdBound,gcdRan⟩ := gcd_executes numerator denominator sign
  obtain ⟨numeratorTime,numeratorBound,numeratorRan⟩ := numerator_executes numerator denominator common.bits sign
  obtain ⟨denominatorTime,denominatorBound,denominatorRan⟩ := denominator_executes numerator denominator common.bits
    (Encoding.value numerator/common).bits sign
  rw [Encoding.value_bits] at numeratorRan denominatorRan
  refine ⟨_,?_,gcdRan.sequence (numeratorRan.sequence denominatorRan)⟩
  have a := EncodingPrograms.normalize_length_le numerator
  have b := EncodingPrograms.normalize_length_le denominator
  rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at a b
  have commonBound := Binary.Gcd.gcd_size_le (Encoding.value numerator) (Encoding.value denominator)
  change common.size ≤ _ at commonBound
  rw [Encoding.bits_length] at numeratorBound denominatorBound
  have firstSquare := Nat.pow_le_pow_left
    (show numerator.length+common.size+1 ≤ 2*(numerator.length+denominator.length+1) by omega) 2
  have secondSquare := Nat.pow_le_pow_left
    (show denominator.length+common.size+1 ≤ 2*(numerator.length+denominator.length+1) by omega) 2
  have squareCube : (numerator.length+denominator.length+1)^2 ≤ (numerator.length+denominator.length+1)^3 := by nlinarith
  have positive := Nat.one_le_pow' 3 (numerator.length+denominator.length)
  nlinarith

end Counting.StackMachine.RationalArithmetic
