import Counting.StackBinaryMultiplyLoop
import Counting.StackEncodingUnframeTotal

namespace Counting.StackMachine.Binary
open Routine EncodingPrograms

abbrev firstParser : Routine 5 := ofProgram (unframeProgram 4 0 2 5)
abbrev secondParser : Routine 5 := ofProgram (unframeProgram 4 0 3 5)
abbrev pairParser : Routine 5 := sequence firstParser secondParser
abbrev parsedMultiply : Routine 5 := sequence pairParser multiplyRoutine

theorem first_parse_executes (first second suffix : List Bool) :
    Executes firstParser (file (Encoding.frame first++Encoding.frame second++suffix) [] [] [] [] [] [])
      (5*first.length+2) (file (Encoding.frame second++suffix) [] first [] [] [] []) := by
  let finish := unframeConfig 4 0 2 5 7 (file [] [] [] [] [] [] [])
    (Encoding.frame second++suffix) first []
  refine ⟨finish,?_,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  · have start : unframeConfig 4 0 2 5 0 (file [] [] [] [] [] [] [])
        (Encoding.frame first++(Encoding.frame second++suffix)) [] [] =
        (⟨0,file (Encoding.frame first++Encoding.frame second++suffix) [] [] [] [] [] []⟩ : Config firstParser.program) := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> simp only [List.append_assoc] <;> rfl
    rw [← start]
    have executed := unframe_frames 4 0 2 5 (by decide) (by decide) (by decide)
      (file [] [] [] [] [] [] []) first (Encoding.frame second++suffix) []
    simp only [List.append_nil] at executed
    exact executed
  · funext r
    fin_cases r <;> rfl

theorem second_parse_executes (first second suffix : List Bool) :
    Executes secondParser (file (Encoding.frame second++suffix) [] first [] [] [] [])
      (5*second.length+2) (file suffix [] first second [] [] []) := by
  let finish := unframeConfig 4 0 3 5 7 (file [] [] first [] [] [] []) suffix second []
  refine ⟨finish,?_,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  · have start : unframeConfig 4 0 3 5 0 (file [] [] first [] [] [] [])
        (Encoding.frame second++suffix) [] [] =
        (⟨0,file (Encoding.frame second++suffix) [] first [] [] [] []⟩ : Config secondParser.program) := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [← start]
    have executed := unframe_frames 4 0 3 5 (by decide) (by decide) (by decide)
      (file [] [] first [] [] [] []) second suffix []
    simp only [List.append_nil] at executed
    exact executed
  · funext r
    fin_cases r <;> rfl

theorem pair_parse_executes (first second suffix : List Bool) :
    Executes pairParser (file (Encoding.frame first++Encoding.frame second++suffix) [] [] [] [] [] [])
      (5*(first.length+second.length)+5) (file suffix [] first second [] [] []) := by
  have composed := (first_parse_executes first second suffix).sequence
    (second_parse_executes first second suffix)
  convert composed using 1
  omega

/-- Parsing and the full schoolbook loop form a single finite routine. -/
theorem parsed_multiply_executes (first second suffix : List Bool) :
    ∃ transitions ≤ 5*(first.length+second.length)+6+
        (12*second.length*(second.length*(first.length+second.length+1)+first.length+second.length+2)+1),
      Executes parsedMultiply (file (Encoding.frame first++Encoding.frame second++suffix) [] [] [] [] [] []) transitions
        (file suffix (multiplyBits first second) (List.replicate second.length false++first) [] [] [] []) := by
  obtain ⟨transitions,bounded,executed⟩ := multiply_payloads first second suffix
  refine ⟨(5*(first.length+second.length)+5)+1+transitions,by omega,
    (pair_parse_executes first second suffix).sequence executed⟩

theorem first_parse_failure (input : List Bool) (invalid : Encoding.unframe input = none) :
    ∃ transitions ≤ 2*input.length+2, ∃ scratch,
      Executes firstParser (file input [] [] [] [] [] []) transitions (file [] [] [] [] [] scratch []) := by
  obtain ⟨transitions,bounded,scratch,executed⟩ := unframe_malformed 4 0 2 5
    (by decide) (by decide) (file [] [] [] [] [] [] []) input [] [] invalid
  refine ⟨transitions,bounded,scratch,unframeConfig 4 0 2 5 8 (file [] [] [] [] [] [] []) [] [] scratch,
    ?_,(unframe_halted _ _ _ _ _ _ _ _).2,?_⟩
  · have start : unframeConfig 4 0 2 5 0 (file [] [] [] [] [] [] []) input [] [] =
        (⟨0,file input [] [] [] [] [] []⟩ : Config firstParser.program) := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [← start]
    exact executed
  · funext r
    fin_cases r <;> rfl

theorem second_parse_failure (input first scratch : List Bool) (invalid : Encoding.unframe input = none) :
    ∃ transitions ≤ 2*input.length+2, ∃ changed,
      Executes secondParser (file input [] first [] [] scratch []) transitions (file [] [] first [] [] changed []) := by
  obtain ⟨transitions,bounded,changed,executed⟩ := unframe_malformed 4 0 3 5
    (by decide) (by decide) (file [] [] first [] [] [] []) input [] scratch invalid
  refine ⟨transitions,bounded,changed,unframeConfig 4 0 3 5 8 (file [] [] first [] [] [] []) [] [] changed,
    ?_,(unframe_halted _ _ _ _ _ _ _ _).2,?_⟩
  · have start : unframeConfig 4 0 3 5 0 (file [] [] first [] [] [] []) input [] scratch =
        (⟨0,file input [] first [] [] scratch []⟩ : Config secondParser.program) := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [← start]
    exact executed
  · funext r
    fin_cases r <;> rfl

theorem empty_multiply_executes (shifted scratch : List Bool) :
    Executes multiplyRoutine (file [] [] shifted [] [] scratch []) 1 (file [] [] shifted [] [] scratch []) := by
  obtain ⟨executed,halted⟩ := bits_empty 3 multiplyBody (rightControl preparePart shiftPart 0) 0
    (file [] [] shifted [] [] scratch []) rfl
  exact ⟨⟨1,file [] [] shifted [] [] scratch []⟩,executed,halted,rfl⟩

end Counting.StackMachine.Binary
