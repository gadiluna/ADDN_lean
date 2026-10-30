import Counting.StackNaturalCall
import Counting.StackBinaryGcdOutput
import Counting.StackBinaryDivisionOutput

namespace Counting.StackMachine.NaturalCall
open Routine

theorem arguments_length (first second : List Bool) :
    (arguments first second).length ≤ 2*(first.length+second.length)+2 := by
  have a := Binary.natural_value_length first
  have b := Binary.natural_value_length second
  change (Encoding.natural.encode (Encoding.value first)++Encoding.natural.encode (Encoding.value second)).length ≤ _
  rw [List.length_append]
  omega

abbrev gcdRoutine : Routine 11 := callNatural Binary.Gcd.gcdRoutine
abbrev divisionRoutine : Routine 11 := callNatural Binary.Division.divisionRoutine

theorem gcd_executes (first second : List Bool) :
    ∃ time ≤ 820000*(first.length+second.length+1)^3,
      Executes gcdRoutine (file first second [] [] [] [] []) time
        (file first second (Nat.gcd (Encoding.value first) (Encoding.value second)).bits [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := call_executes Binary.Gcd.gcdRoutine Binary.Gcd.gcdFunction
    (Complexity.polynomial 1000 3) Binary.Gcd.gcd_computes Nat.gcd Binary.Gcd.gcdFunction_natural first second
  refine ⟨time,bounded.trans ?_,ran⟩
  have encoded := arguments_length first second
  have power := Nat.pow_le_pow_left
    (show (arguments first second).length+1 ≤ 3*(first.length+second.length+1) by omega) 3
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (first.length+second.length)
    have product := Nat.mul_le_mul_left (first.length+second.length+1) square
    nlinarith
  change 30*(1000*((arguments first second).length+1)^3+(arguments first second).length+first.length+second.length+10) ≤ _
  nlinarith

theorem division_executes (first second : List Bool) :
    ∃ time ≤ 50000*(first.length+second.length+1)^2,
      Executes divisionRoutine (file first second [] [] [] [] []) time
        (file first second (Encoding.value first/Encoding.value second).bits [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := call_executes Binary.Division.divisionRoutine Binary.Division.quotientFunction
    (Complexity.polynomial 180 2) Binary.Division.division_computes (· / ·) Binary.Division.quotientFunction_natural first second
  refine ⟨time,bounded.trans ?_,ran⟩
  have encoded := arguments_length first second
  have power := Nat.pow_le_pow_left
    (show (arguments first second).length+1 ≤ 3*(first.length+second.length+1) by omega) 2
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^2 := by nlinarith
  change 30*(180*((arguments first second).length+1)^2+(arguments first second).length+first.length+second.length+10) ≤ _
  nlinarith

end Counting.StackMachine.NaturalCall
