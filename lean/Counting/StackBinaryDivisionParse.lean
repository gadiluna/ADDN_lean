import Counting.StackBinaryDivisionLoop
import Counting.StackEncodingPairSemantics
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Binary.Division
open Routine EncodingPrograms

def parseRoles : Fin 5 → Fin 10 := ![0,6,2,8,5]

theorem parseRoles_injective : Function.Injective parseRoles := by decide

abbrev parser : Routine 8 := pairRoutine 5 parseRoles
abbrev reverseInput : Routine 8 := ofProgram (ListPrograms.reverseProgram 8 6 4)
abbrev prepare : Routine 8 := sequence parser (sequence (clear 5) reverseInput)
abbrev parsedDivision : Routine 8 := sequence prepare routine

theorem prepare_executes (input : List Bool) :
    ∃ transitions ≤ 8*input.length+18,
      Executes prepare (file input [] [] [] [] [] [] [] [] []) transitions
        (file (parsePair input).suffix [] (parsePair input).second [] (parsePair input).first.reverse [] [] [] [] []) := by
  let parsed := parsePair input
  obtain ⟨parseTime,parseBound,executed⟩ := pair_executes_spec 5 parseRoles parseRoles_injective
    (file input [] [] [] [] [] [] [] [] []) rfl
  have parsedStore : pairExpected 5 parseRoles (file input [] [] [] [] [] [] [] [] []) =
      file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] [] := by
    funext r
    fin_cases r <;> simp [pairExpected,parseRoles,file,parsed]
  rw [parsedStore] at executed
  have cleared := clear_executes (registers := 8) 5
    (file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] [])
  have clearedStore : Function.update (file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 5 [] =
      file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] [] := by
    funext r
    fin_cases r <;> rfl
  change Executes (clear 5) (file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 2
    (Function.update (file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 5 []) at cleared
  rw [clearedStore] at cleared
  have reversed := reverse_executes 8 6 4 (by decide)
    (file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] [])
  change Executes reverseInput (file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] [])
    (2*parsed.first.length+1)
    (Function.update (Function.update (file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] []) 6 []) 4
      (parsed.first.reverse++[])) at reversed
  have reversedStore : Function.update (Function.update (file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] []) 6 []) 4
      (parsed.first.reverse++[]) = file parsed.suffix [] parsed.second [] parsed.first.reverse [] [] [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [reversedStore] at reversed
  refine ⟨parseTime+1+(2+1+(2*parsed.first.length+1)),?_,executed.sequence (cleared.sequence reversed)⟩
  have lengths := parsePair_length_bound input
  change parsed.first.length+parsed.second.length+parsed.suffix.length ≤ input.length at lengths
  change parseTime ≤ 6*input.length+13 at parseBound
  omega

/-- All parsing outcomes reach the same bounded loop. A failed parse has
zero second payload, and the final zero-divisor branch handles it. -/
theorem parsed_division_executes (input : List Bool) :
    ∃ transitions ≤ 120*(input.length+1)^2,
      Executes parsedDivision (file input [] [] [] [] [] [] [] [] []) transitions
        (file (parsePair input).suffix
          (divideBits (parsePair input).first (parsePair input).second).1 (parsePair input).second
          (divideBits (parsePair input).first (parsePair input).second).2 [] [] [] [] [] []) := by
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepare_executes input
  obtain ⟨divideTime,divideBound,divided⟩ := divide_payloads (parsePair input).suffix (parsePair input).first (parsePair input).second
  refine ⟨prepareTime+1+divideTime,?_,prepared.sequence divided⟩
  have lengths := parsePair_length_bound input
  have aBound : (parsePair input).first.length ≤ input.length := by omega
  have bBound : 2*(parsePair input).second.length+(parsePair input).first.length+2 ≤ 2*input.length+2 := by omega
  have product := Nat.mul_le_mul aBound bBound
  nlinarith

end Counting.StackMachine.Binary.Division
