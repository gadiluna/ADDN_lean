import Counting.EncodingSigned
import Counting.StackBinaryCompareBits
import Counting.StackBinarySubtractBits

namespace Counting.StackMachine.Signed
open Binary Arithmetic

def value (negative : Bool) (magnitude : List Bool) : Int :=
  Encoding.signedValue negative (Encoding.value magnitude)

def addBits (firstSign secondSign : Bool) (first second : List Bool) : Bool × List Bool :=
  if firstSign = secondSign then (firstSign,Arithmetic.addBits false first second)
  else if compareBits true first second then
    (secondSign,(subtractBits false second first).1)
  else (firstSign,(subtractBits false first second).1)

theorem addBits_value (firstSign secondSign : Bool) (first second : List Bool) :
    value (addBits firstSign secondSign first second).1
      (addBits firstSign secondSign first second).2 =
    value firstSign first + value secondSign second := by
  have sum := Arithmetic.addBits_value false first second
  simp only [Bool.toNat_false,Nat.add_zero] at sum
  have comparison := compareBits_le first second
  by_cases equal : firstSign = secondSign
  · subst secondSign
    simp only [addBits,ite_true,value,sum]
    cases firstSign <;> simp [Encoding.signedValue,add_comm]
  · by_cases ordered : compareBits true first second = true
    · have difference := subtractBits_of_le false second first
        (by simpa using comparison.mp ordered)
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at difference
      simp only [addBits,if_neg equal,ordered,ite_true,value,difference]
      have order := comparison.mp ordered
      cases firstSign <;> cases secondSign <;> simp_all [Encoding.signedValue] <;> omega
    · have difference := subtractBits_of_le false first second
        (by have := comparison.not.mp ordered; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]; omega)
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at difference
      simp only [addBits,if_neg equal,if_neg ordered,value,difference]
      have order := comparison.not.mp ordered
      cases firstSign <;> cases secondSign <;> simp_all [Encoding.signedValue] <;> omega

theorem addBits_length (firstSign secondSign : Bool) (first second : List Bool) :
    (addBits firstSign secondSign first second).2.length ≤ first.length+second.length+1 := by
  unfold addBits
  split_ifs
  · exact Arithmetic.addBits_length false first second
  · simp only [subtractBits_length]; omega
  · simp only [subtractBits_length]; omega

end Counting.StackMachine.Signed
