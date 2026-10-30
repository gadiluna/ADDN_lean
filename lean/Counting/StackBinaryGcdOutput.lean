import Counting.StackBinaryGcdInitialize
import Counting.StackBinaryGcdLoop

namespace Counting.StackMachine.Binary.Gcd
open Routine EncodingPrograms

abbrev formatOutput : Routine 8 := Normalize.formatRoutine 7 6 1 8
abbrev gcdRoutine : Routine 8 := sequence initialization (sequence routine formatOutput)

def gcdFunction (input : List Bool) : List Bool :=
  let parsed := parsePair input
  Encoding.natural.encode (Nat.gcd (Encoding.value parsed.first) (Encoding.value parsed.second))

theorem gcd_size_le (first second : Nat) : (Nat.gcd first second).size ≤ first.size+second.size := by
  by_cases zero : first=0
  · simp [zero]
  · have bounded := Nat.size_le_size (Nat.gcd_le_left second (Nat.pos_of_ne_zero zero))
    omega

/-- The generated unary counter contains O(input bits) elements. Every
Euclidean step performs binary long division; no loop iterates up to the
value of either operand. All words have a uniform cubic stack bound. -/
theorem gcd_computes : ComputesIn gcdRoutine.program gcdFunction (Complexity.polynomial 1000 3) := by
  intro input
  let parsed := parsePair input
  let first := Encoding.value parsed.first
  let second := Encoding.value parsed.second
  obtain ⟨initialTime,initialBound,initialized⟩ := initialize_executes input
  obtain ⟨loopTime,loopBound,executed⟩ := gcd_payloads first second
  have formatted := Normalize.format_executes 7 6 1 8 (by decide) (by decide) (by decide)
    (file [] (Nat.gcd first second) 0) rfl
  change Executes formatOutput (file [] (Nat.gcd first second) 0)
    (Normalize.formatCost (Nat.gcd first second).bits)
    (Function.update (Function.update (file [] (Nat.gcd first second) 0) 6 []) 1
      (Encoding.natural.encode (Encoding.value (Nat.gcd first second).bits)++[])) at formatted
  rw [Encoding.value_bits,List.append_nil] at formatted
  obtain ⟨finish,ran,halted,stored⟩ := initialized.sequence (executed.sequence formatted)
  refine ⟨initialTime+1+(loopTime+1+Normalize.formatCost (Nat.gcd first second).bits),finish,?_,⟨?_,halted⟩,?_⟩
  · have firstBound := normalize_length_le parsed.first
    have secondBound := normalize_length_le parsed.second
    rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at firstBound secondBound
    change first.size ≤ parsed.first.length at firstBound
    change second.size ≤ parsed.second.length at secondBound
    have lengths := parsePair_length_bound input
    change parsed.first.length+parsed.second.length+parsed.suffix.length ≤ input.length at lengths
    have finalBound := Normalize.formatCost_le (Nat.gcd first second).bits
    rw [Encoding.bits_length] at finalBound
    have gcdSize := gcd_size_le first second
    have factors : (2*second.size+1)*(first.size+second.size+1)^2 ≤ 2*(input.length+1)^3 := by
      have firstFactor : 2*second.size+1 ≤ 2*(input.length+1) := by omega
      have secondFactor : (first.size+second.size+1)^2 ≤ (input.length+1)^2 :=
        Nat.pow_le_pow_left (by omega) 2
      have product := Nat.mul_le_mul firstFactor secondFactor
      nlinarith
    have cube : input.length+1 ≤ (input.length+1)^3 := by
      have square := Nat.one_le_pow' 2 input.length
      have product := Nat.mul_le_mul_left (input.length+1) square
      nlinarith
    change initialTime+1+(loopTime+1+Normalize.formatCost (Nat.gcd first second).bits) ≤ 1000*(input.length+1)^3
    nlinarith
  · have start : initial gcdRoutine.program input = ⟨0,Division.file input [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored,Function.update_self]
    rfl

theorem gcdFunction_natural (first second : Nat) :
    gcdFunction ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) =
      Encoding.natural.encode (Nat.gcd first second) := by
  have parsed := parsePair_frames first.bits second.bits []
  simp only [List.append_nil] at parsed
  change Encoding.natural.encode (Nat.gcd
    (Encoding.value (parsePair (Encoding.frame first.bits++Encoding.frame second.bits)).first)
    (Encoding.value (parsePair (Encoding.frame first.bits++Encoding.frame second.bits)).second)) = _
  rw [parsed,Encoding.value_bits,Encoding.value_bits]

end Counting.StackMachine.Binary.Gcd
