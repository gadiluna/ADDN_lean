import Counting.StackSignedParser

namespace Counting.StackMachine.Signed
open Routine

abbrev parser : Routine 10 := sequence (readOperand false) (readOperand true)
abbrev parsedAddition : Routine 10 := sequence parser additionRoutine

def parsedFirst (input : List Bool) : Bool × List Bool := (operandSign input,operandMagnitude input)
def parsedSecond (input : List Bool) : Bool × List Bool := parsedFirst (operandSuffix input)
def parsedSuffix (input : List Bool) : List Bool := operandSuffix (operandSuffix input)
def sumPayload (input : List Bool) : Bool × List Bool :=
  addBits (parsedFirst input).1 (parsedSecond input).1 (parsedFirst input).2 (parsedSecond input).2

theorem parser_executes (input : List Bool) :
    ∃ time ≤ 6*input.length+21,
      Executes parser (file input [] [] [] [] [] [] [] []) time
        (file (parsedSuffix input) (parsedFirst input).2 (parsedSecond input).2
          [(parsedFirst input).1] [(parsedSecond input).1] [] [] [] []) := by
  obtain ⟨firstTime,firstBound,firstRun⟩ := readOperand_executes false (file input [] [] [] [] [] [] [] []) rfl rfl
  have firstResult : operandResult false (file input [] [] [] [] [] [] [] []) =
      file (operandSuffix input) (operandMagnitude input) [] [operandSign input] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [operandResult,file,readRoles]
  rw [firstResult] at firstRun
  obtain ⟨secondTime,secondBound,secondRun⟩ := readOperand_executes true
    (file (operandSuffix input) (operandMagnitude input) [] [operandSign input] [] [] [] [] []) rfl rfl
  have secondResult : operandResult true
      (file (operandSuffix input) (operandMagnitude input) [] [operandSign input] [] [] [] [] []) =
      file (parsedSuffix input) (parsedFirst input).2 (parsedSecond input).2
        [(parsedFirst input).1] [(parsedSecond input).1] [] [] [] [] := by
    funext r; fin_cases r <;> simp [operandResult,file,readRoles,parsedFirst,parsedSecond,parsedSuffix]
  rw [secondResult] at secondRun
  refine ⟨_,?_,firstRun.sequence secondRun⟩
  change firstTime ≤ 3*input.length+10 at firstBound
  change secondTime ≤ 3*(operandSuffix input).length+10 at secondBound
  have length := operand_length input
  omega

theorem parsed_lengths (input : List Bool) :
    (parsedFirst input).2.length+(parsedSecond input).2.length+(parsedSuffix input).length ≤ input.length := by
  have first := operand_length input
  have second := operand_length (operandSuffix input)
  change (operandMagnitude input).length+(operandMagnitude (operandSuffix input)).length+
    (operandSuffix (operandSuffix input)).length ≤ input.length
  omega

theorem sumPayload_length (input : List Bool) : (sumPayload input).2.length ≤ input.length+1 := by
  have bound := addBits_length (parsedFirst input).1 (parsedSecond input).1 (parsedFirst input).2 (parsedSecond input).2
  have lengths := parsed_lengths input
  exact bound.trans (by omega)

theorem parsed_addition_executes (input : List Bool) :
    ∃ time ≤ 18*input.length+41,
      Executes parsedAddition (file input [] [] [] [] [] [] [] []) time
        (file (parsedSuffix input) [] [] [] [] (sumPayload input).2 [(sumPayload input).1] [] []) := by
  obtain ⟨parseTime,parseBound,parsed⟩ := parser_executes input
  obtain ⟨addTime,addBound,added⟩ := addition_executes
    (parsedFirst input).1 (parsedSecond input).1 (parsedSuffix input) (parsedFirst input).2 (parsedSecond input).2
  refine ⟨_,?_,parsed.sequence added⟩
  have lengths := parsed_lengths input
  omega

def signedAdditionFunction (input : List Bool) : List Bool :=
  Encoding.integer.encode (value (parsedFirst input).1 (parsedFirst input).2+
    value (parsedSecond input).1 (parsedSecond input).2)

theorem sumPayload_value (input : List Bool) :
    value (sumPayload input).1 (sumPayload input).2 =
    value (parsedFirst input).1 (parsedFirst input).2+value (parsedSecond input).1 (parsedSecond input).2 :=
  addBits_value _ _ _ _

theorem parsedFirst_integer (integer : Int) (suffix : List Bool) :
    parsedFirst (Encoding.integer.encode integer++suffix) = (Encoding.negative integer,integer.natAbs.bits) := by
  simp [parsedFirst,operandSign,operandMagnitude,Encoding.integer_encode,Encoding.natural,
    EncodingPrograms.unframePayload]

theorem operandSuffix_integer (integer : Int) (suffix : List Bool) :
    operandSuffix (Encoding.integer.encode integer++suffix) = suffix := by
  simp [operandSuffix,Encoding.integer_encode,Encoding.natural,EncodingPrograms.unframeSuffix]

theorem signedAdditionFunction_integer (first second : Int) :
    signedAdditionFunction ((Encoding.product Encoding.integer Encoding.integer).encode (first,second)) =
      Encoding.integer.encode (first+second) := by
  change Encoding.integer.encode (value (parsedFirst (Encoding.integer.encode first++Encoding.integer.encode second)).1
    (parsedFirst (Encoding.integer.encode first++Encoding.integer.encode second)).2+
    value (parsedSecond (Encoding.integer.encode first++Encoding.integer.encode second)).1
    (parsedSecond (Encoding.integer.encode first++Encoding.integer.encode second)).2) = _
  rw [parsedFirst_integer]
  simp only [parsedSecond,operandSuffix_integer]
  have last := parsedFirst_integer second []
  simp only [List.append_nil] at last
  rw [last]
  simp only [value,Encoding.value_bits,Encoding.signedValue_negative_natAbs]

end Counting.StackMachine.Signed
