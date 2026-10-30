import Counting.StackNaturalCallArithmetic

namespace Counting.StackMachine.NaturalCall
open Routine

def paddedAddresses : Fin 7 ↪ Fin 10 := ⟨fun index => ⟨index.val,by omega⟩,
  by intro a b equal; exact Fin.ext (congrArg (fun index : Fin 10 => index.val) equal)⟩

abbrev paddedMultiply : Routine 8 := relocate Binary.multiplicationRoutine paddedAddresses
abbrev multiplicationRoutine : Routine 11 := callNatural paddedMultiply

theorem multiplication_executes (first second : List Bool) :
    ∃ time ≤ 82000*(first.length+second.length+1)^3,
      Executes multiplicationRoutine (file first second [] [] [] [] []) time
        (file first second (Encoding.value first*Encoding.value second).bits [] [] [] []) := by
  have computes := relocate_computes Binary.multiplicationRoutine paddedAddresses rfl rfl
    Binary.productFunction (Complexity.polynomial 100 3) Binary.multiplication_computes
  obtain ⟨time,bounded,ran⟩ := call_executes paddedMultiply Binary.productFunction
    (Complexity.polynomial 100 3) computes (· * ·) Binary.productFunction_natural first second
  refine ⟨time,bounded.trans ?_,ran⟩
  have encoded := arguments_length first second
  have power := Nat.pow_le_pow_left
    (show (arguments first second).length+1 ≤ 3*(first.length+second.length+1) by omega) 3
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (first.length+second.length)
    have product := Nat.mul_le_mul_left (first.length+second.length+1) square
    nlinarith
  change 30*(100*((arguments first second).length+1)^3+(arguments first second).length+first.length+second.length+10) ≤ _
  nlinarith

theorem product_bits_length (first second : List Bool) :
    (Encoding.value first*Encoding.value second).bits.length ≤ first.length+second.length := by
  rw [Encoding.bits_length_le_iff,pow_add]
  have a := Binary.value_lt_pow_length first
  have b := Binary.value_lt_pow_length second
  have product := Nat.mul_le_mul
    (show Encoding.value first+1 ≤ 2^first.length by omega)
    (show Encoding.value second+1 ≤ 2^second.length by omega)
  nlinarith

end Counting.StackMachine.NaturalCall
