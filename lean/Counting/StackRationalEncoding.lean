import Counting.StackRationalNormalize
import Counting.StackEncodingPairSemantics

namespace Counting.StackMachine.RationalArithmetic
open Routine EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def parsed (input : List Bool) : PairParseResult := parsePair input.tail
def parsedSign (input : List Bool) : Bool := input.headD false

/-- This total extension retains a completed numerator and treats an absent
denominator as zero. Canonical inputs are characterized separately below. -/
def normalizationFunction (input : List Bool) : List Bool :=
  Encoding.rational.encode (mkRat
    (Encoding.signedValue (parsedSign input) (Encoding.value (parsed input).first))
    (Encoding.value (parsed input).second))

def parseRoles : Fin 5 → Fin 16 := ![6,0,1,7,8]
abbrev moveInput : Routine 14 := move 13 0 6 7
abbrev rationalParser : Routine 14 := sequence moveInput
  (sequence (Signed.readSign 6 5)
    (sequence (pairRoutine 11 parseRoles) (sequence (clear 6) (clear 8))))

def parserFile (input numerator denominator sign status : List Bool) : Fin 16 → List Bool :=
  ![numerator,denominator,[],[],[],sign,input,[],status,[],[],[],[],[],[],[]]

theorem rationalParser_executes (input : List Bool) :
    ∃ time ≤ 13*input.length+28,
      Executes rationalParser (file input [] [] [] [] []) time
        (file (parsed input).first (parsed input).second [] [] [] [parsedSign input]) := by
  have moved := move_executes 13 0 6 7 (by decide) (by decide) (by decide)
    (file input [] [] [] [] []) rfl
  have moveStore : Function.update (Function.update (file input [] [] [] [] []) 6
      (input++[])) 0 [] = parserFile input [] [] [] [] := by
    funext r; fin_cases r <;> simp [file,parserFile]
  change Executes moveInput (file input [] [] [] [] []) (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] []) 6 (input++[])) 0 []) at moved
  rw [moveStore] at moved
  have signed := Signed.readSign_executes (registers := 14) 6 5 (by decide)
    (parserFile input [] [] [] [])
  have signStore : Function.update (Function.update (parserFile input [] [] [] []) 6 input.tail) 5
      [input.headD false] = parserFile input.tail [] [] [parsedSign input] [] := by
    funext r; fin_cases r <;> rfl
  change Executes (Signed.readSign 6 5) (parserFile input [] [] [] []) 2
    (Function.update (Function.update (parserFile input [] [] [] []) 6 input.tail) 5
      [input.headD false]) at signed
  rw [signStore] at signed
  obtain ⟨parseTime,parseBound,ran⟩ := pair_executes_spec 11 parseRoles (by decide)
    (parserFile input.tail [] [] [parsedSign input] []) rfl
  have parseStore : pairExpected 11 parseRoles (parserFile input.tail [] [] [parsedSign input] []) =
      parserFile (parsed input).suffix (parsed input).first (parsed input).second
        [parsedSign input] [(parsed input).accepted] := by
    funext r; fin_cases r <;> simp [pairExpected,parseRoles,parserFile,parsed]
  rw [parseStore] at ran
  have clearedSuffix := clear_executes (registers := 14) 6
    (parserFile (parsed input).suffix (parsed input).first (parsed input).second
      [parsedSign input] [(parsed input).accepted])
  have suffixStore : Function.update
      (parserFile (parsed input).suffix (parsed input).first (parsed input).second
        [parsedSign input] [(parsed input).accepted]) 6 [] =
      parserFile [] (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted] := by
    funext r; fin_cases r <;> rfl
  change Executes (clear 6) _ ((parsed input).suffix.length+1) _ at clearedSuffix
  rw [suffixStore] at clearedSuffix
  have clearedFlag := clear_executes (registers := 14) 8
    (parserFile [] (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted])
  have finalStore : Function.update
      (parserFile [] (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted]) 8 [] =
      file (parsed input).first (parsed input).second [] [] [] [parsedSign input] := by
    funext r; fin_cases r <;> rfl
  change Executes (clear 8) _ 2 _ at clearedFlag
  rw [finalStore] at clearedFlag
  refine ⟨_,?_,moved.sequence (signed.sequence (ran.sequence (clearedSuffix.sequence clearedFlag)))⟩
  change parseTime ≤ 6*input.tail.length+13 at parseBound
  have lengths := parsePair_length_bound input.tail
  change (parsed input).first.length+(parsed input).second.length+(parsed input).suffix.length ≤ input.tail.length at lengths
  have tail : input.tail.length ≤ input.length := by simp
  omega

theorem parsed_lengths (input : List Bool) :
    (parsed input).first.length+(parsed input).second.length ≤ input.length := by
  have bounded := parsePair_length_bound input.tail
  have tail : input.tail.length ≤ input.length := by simp
  change (parsed input).first.length+(parsed input).second.length+(parsed input).suffix.length ≤ input.tail.length at bounded
  omega

theorem normalizationFunction_raw (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) :
    normalizationFunction (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)) =
      Encoding.rational.encode (mkRat (Encoding.signedValue sign numerator) denominator) := by
  simp only [normalizationFunction,parsedSign,List.headD_cons,parsed,List.tail_cons,
    Encoding.natural,parsePair_frames,Encoding.value_bits]

theorem normalizationFunction_rational (value : Rat) :
    normalizationFunction (Encoding.rational.encode value) = Encoding.rational.encode value := by
  rw [Encoding.rational_encode,Encoding.integer_encode,List.cons_append]
  have raw := normalizationFunction_raw (Encoding.negative value.num) value.num.natAbs value.den []
  simp only [List.append_nil,Encoding.signedValue_negative_natAbs,Rat.mkRat_self] at raw
  exact raw

end Counting.StackMachine.RationalArithmetic
