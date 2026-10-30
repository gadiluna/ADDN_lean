import Counting.StackRationalReader

namespace Counting.StackMachine.RationalArithmetic.Pair
open Routine

def file (a b c d sa sc input : List Bool) : Fin 9 → List Bool := ![a,b,c,d,sa,sc,input,[],[]]
def firstRoles : Fin 6 ↪ Fin 9 := ⟨![6,0,1,4,7,8],by decide⟩
def secondRoles : Fin 6 ↪ Fin 9 := ⟨![6,2,3,5,7,8],by decide⟩
abbrev firstReader : Routine 7 := relocate Reader.reader firstRoles
abbrev secondReader : Routine 7 := relocate Reader.reader secondRoles
abbrev parser : Routine 7 := sequence (move 6 0 6 7)
  (sequence firstReader (sequence secondReader (clear 6)))

def secondInput (input : List Bool) : List Bool := (parsed input).suffix
def first (input : List Bool) : EncodingPrograms.PairParseResult := parsed input
def second (input : List Bool) : EncodingPrograms.PairParseResult := parsed (secondInput input)
def firstSign (input : List Bool) : Bool := parsedSign input
def secondSign (input : List Bool) : Bool := parsedSign (secondInput input)
def result (input : List Bool) : Fin 9 → List Bool :=
  file (first input).first (first input).second (second input).first (second input).second
    [firstSign input] [secondSign input] []

theorem first_executes (input : List Bool) :
    ∃ time ≤ 6*input.length+19,
      Executes firstReader (file [] [] [] [] [] [] input) time
        (file (first input).first (first input).second [] [] [firstSign input] [] (secondInput input)) := by
  obtain ⟨time,bounded,ran⟩ := Reader.reader_executes input
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Reader.reader firstRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,Reader.file,firstRoles]
  · intro r; fin_cases r <;> simp [file,Reader.file,firstRoles,first,firstSign,secondInput]
  · intro r outside
    fin_cases r
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 2 rfl)
    · simp [file]
    · simp [file]
    · exact False.elim (outside 3 rfl)
    · simp [file]
    · exact False.elim (outside 0 rfl)
    all_goals simp [file]

theorem second_executes (a b sa input : List Bool) :
    ∃ time ≤ 6*input.length+19,
      Executes secondReader (file a b [] [] sa [] input) time
        (file a b (parsed input).first (parsed input).second sa [parsedSign input] (parsed input).suffix) := by
  obtain ⟨time,bounded,ran⟩ := Reader.reader_executes input
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Reader.reader secondRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,Reader.file,secondRoles]
  · intro r; fin_cases r <;> simp [file,Reader.file,secondRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 2 rfl)
    · simp [file]
    · exact False.elim (outside 3 rfl)
    · exact False.elim (outside 0 rfl)
    all_goals simp [file]

theorem parsed_lengths (input : List Bool) :
    (first input).first.length+(first input).second.length+
      (second input).first.length+(second input).second.length+(second input).suffix.length ≤ input.length := by
  have firstBound := EncodingPrograms.parsePair_length_bound input.tail
  have secondBound := EncodingPrograms.parsePair_length_bound (secondInput input).tail
  have firstTail : input.tail.length ≤ input.length := by simp
  have secondTail : (secondInput input).tail.length ≤ (secondInput input).length := by simp
  change (first input).first.length+(first input).second.length+(secondInput input).length ≤ input.tail.length at firstBound
  change (second input).first.length+(second input).second.length+(second input).suffix.length ≤ (secondInput input).tail.length at secondBound
  omega

theorem parser_executes (input : List Bool) :
    ∃ time ≤ 19*input.length+46,
      Executes parser (file input [] [] [] [] [] []) time (result input) := by
  have moved := move_executes 6 0 6 7 (by decide) (by decide) (by decide) (file input [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] [] [] [] []) 6 (input++[])) 0 [] =
      file [] [] [] [] [] [] input := by
    funext r; fin_cases r <;> simp [file]
  change Executes (move 6 0 6 7) _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] [] []) 6 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  obtain ⟨firstTime,firstBound,firstRan⟩ := first_executes input
  obtain ⟨secondTime,secondBound,secondRan⟩ := second_executes (first input).first (first input).second [firstSign input] (secondInput input)
  have cleared := clear_executes (registers := 7) 6
    (file (first input).first (first input).second (second input).first (second input).second
      [firstSign input] [secondSign input] (second input).suffix)
  have clearStore : Function.update
      (file (first input).first (first input).second (second input).first (second input).second
        [firstSign input] [secondSign input] (second input).suffix) 6 [] = result input := by
    funext r; fin_cases r <;> simp [file,result]
  change Executes (clear 6) _ ((second input).suffix.length+1) _ at cleared
  rw [clearStore] at cleared
  refine ⟨_,?_,moved.sequence (firstRan.sequence (secondRan.sequence cleared))⟩
  have split := EncodingPrograms.parsePair_length_bound input.tail
  have tail : input.tail.length ≤ input.length := by simp
  change _+_+(secondInput input).length ≤ _ at split
  have lengths := parsed_lengths input
  omega

end Counting.StackMachine.RationalArithmetic.Pair
