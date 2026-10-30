import Counting.StackSignedMultiply

namespace Counting.StackMachine.Signed.Multiply
open Routine

theorem signedProduct_computes :
    ComputesIn productRoutine.program signedProductFunction (Complexity.polynomial 100 3) := by
  intro input
  obtain ⟨parseTime,parseBound,parsed⟩ := parser_executes input
  obtain ⟨multiplyTime,multiplyBound,multiplied⟩ := productCore_executes (parsedSuffix input)
    (parsedFirst input).2 (parsedSecond input).2 (parsedFirst input).1 (parsedSecond input).1
  obtain ⟨formatTime,formatBound,formatted⟩ := formatOutput_executes (parsedSuffix input)
    (Binary.multiplyBits (parsedFirst input).2 (parsedSecond input).2)
    (xor (parsedFirst input).1 (parsedSecond input).1)
  obtain ⟨finish,ran,halted,stored⟩ := (parsed.sequence multiplied).sequence formatted
  refine ⟨parseTime+1+multiplyTime+1+formatTime,finish,?_,⟨?_,halted⟩,?_⟩
  · have lengths := parsed_lengths input
    have multiplyLimit := Nat.pow_le_pow_left
      (show (parsedFirst input).2.length+(parsedSecond input).2.length+1 ≤ input.length+1 by omega) 3
    have payload := Binary.multiplyBits_length (parsedFirst input).2 (parsedSecond input).2
    have payloadLimit := Nat.mul_le_mul
      (show (parsedSecond input).2.length ≤ input.length+1 by omega)
      (show (parsedFirst input).2.length+(parsedSecond input).2.length+1 ≤ input.length+1 by omega)
    have squareCube : (input.length+1)^2 ≤ (input.length+1)^3 := by nlinarith
    have linearCube : input.length+1 ≤ (input.length+1)^3 := by
      have square := Nat.one_le_pow' 2 input.length
      have product := Nat.mul_le_mul_left (input.length+1) square
      nlinarith
    change parseTime+1+multiplyTime+1+formatTime ≤ 100*(input.length+1)^3
    nlinarith
  · have start : initial productRoutine.program input = ⟨0,file input [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (value (xor (parsedFirst input).1 (parsedSecond input).1)
      (Binary.multiplyBits (parsedFirst input).2 (parsedSecond input).2)) = _
    rw [product_value]
    rfl

theorem signedProductFunction_integer (first second : Int) :
    signedProductFunction ((Encoding.product Encoding.integer Encoding.integer).encode (first,second)) =
      Encoding.integer.encode (first*second) := by
  change Encoding.integer.encode (value (parsedFirst (Encoding.integer.encode first++Encoding.integer.encode second)).1
    (parsedFirst (Encoding.integer.encode first++Encoding.integer.encode second)).2*
    value (parsedSecond (Encoding.integer.encode first++Encoding.integer.encode second)).1
    (parsedSecond (Encoding.integer.encode first++Encoding.integer.encode second)).2) = _
  rw [parsedFirst_integer]
  simp only [parsedSecond,operandSuffix_integer]
  have last := parsedFirst_integer second []
  simp only [List.append_nil] at last
  rw [last]
  simp only [value,Encoding.value_bits,Encoding.signedValue_negative_natAbs]

end Counting.StackMachine.Signed.Multiply
