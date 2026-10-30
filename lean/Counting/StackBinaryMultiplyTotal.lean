import Counting.StackBinaryMultiplyParse

namespace Counting.StackMachine.Binary
open Routine EncodingPrograms

def productPayload (input : List Bool) : List Bool :=
  match Encoding.unframe input with
  | none => []
  | some (first,rest) => match Encoding.unframe rest with
    | none => []
    | some (second,_) => multiplyBits first second

def productFunction (input : List Bool) : List Bool := Encoding.natural.encode (Encoding.value (productPayload input))

theorem cubic_dominates_linear (length : Nat) : length+1 ≤ (length+1)^3 := by
  have square : 1 ≤ (length+1)^2 := Nat.one_le_pow' 2 length
  have multiplied := Nat.mul_le_mul_left (length+1) square
  nlinarith

theorem parsed_multiply_total (input : List Bool) :
    ∃ transitions ≤ 40*(input.length+1)^3, ∃ suffix shifted scratch,
      Executes parsedMultiply (file input [] [] [] [] [] []) transitions
        (file suffix (productPayload input) shifted [] [] scratch []) := by
  cases firstParsed : Encoding.unframe input with
  | none =>
      obtain ⟨firstTime,firstBound,firstScratch,firstRun⟩ := first_parse_failure input firstParsed
      obtain ⟨secondTime,secondBound,secondScratch,secondRun⟩ := second_parse_failure [] [] firstScratch rfl
      have parsed := firstRun.sequence secondRun
      have ran := parsed.sequence (empty_multiply_executes [] secondScratch)
      refine ⟨(firstTime+1+secondTime)+1+1,?_,[],[],secondScratch,?_⟩
      · have power := cubic_dominates_linear input.length
        simp only [List.length_nil] at secondBound
        omega
      · simpa only [productPayload,firstParsed] using ran
  | some pair =>
      obtain ⟨first,rest⟩ := pair
      have split := Machine.unframe_sound input first rest firstParsed
      cases secondParsed : Encoding.unframe rest with
      | none =>
          obtain ⟨secondTime,secondBound,scratch,secondRun⟩ := second_parse_failure rest first [] secondParsed
          have parsed : Executes pairParser (file input [] [] [] [] [] [])
              ((5*first.length+2)+1+secondTime) (file [] [] first [] [] scratch []) := by
            have start : Executes firstParser (file input [] [] [] [] [] [])
                (5*first.length+2) (file rest [] first [] [] [] []) := by
              have executed := unframe_frames 4 0 2 5 (by decide) (by decide) (by decide)
                (file [] [] [] [] [] [] []) first rest []
              refine ⟨unframeConfig 4 0 2 5 7 (file [] [] [] [] [] [] []) rest first [],?_,
                (unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
              · have initialFile : unframeConfig 4 0 2 5 0 (file [] [] [] [] [] [] [])
                    (Encoding.frame first++rest) [] [] =
                    (⟨0,file input [] [] [] [] [] []⟩ : Config firstParser.program) := by
                  rw [split]
                  apply congrArg (Config.mk _)
                  funext r
                  fin_cases r <;> rfl
                rw [← initialFile]
                simp only [List.append_nil] at executed
                exact executed
              · funext r
                fin_cases r <;> rfl
            exact start.sequence secondRun
          refine ⟨((5*first.length+2)+1+secondTime)+1+1,?_,[],first,scratch,?_⟩
          · have length : input.length=2*first.length+1+rest.length := by
              rw [split,List.length_append,Encoding.frame_length]
            have power := cubic_dominates_linear input.length
            omega
          · simpa only [productPayload,firstParsed,secondParsed] using
              parsed.sequence (empty_multiply_executes first scratch)
      | some pair =>
          obtain ⟨second,suffix⟩ := pair
          have splitSecond := Machine.unframe_sound rest second suffix secondParsed
          obtain ⟨transitions,bounded,executed⟩ := parsed_multiply_executes first second suffix
          refine ⟨transitions,?_,suffix,List.replicate second.length false++first,[],?_⟩
          · have length : first.length+second.length ≤ input.length := by
              rw [split,splitSecond,List.length_append,List.length_append,Encoding.frame_length,Encoding.frame_length]
              omega
            have secondLength : second.length ≤ input.length := by omega
            have larger : 5*(first.length+second.length)+6+
                  (12*second.length*(second.length*(first.length+second.length+1)+first.length+second.length+2)+1) ≤
                5*input.length+6+(12*input.length*(input.length*(input.length+1)+input.length+2)+1) := by
              have product : second.length*(first.length+second.length+1) ≤
                  input.length*(input.length+1) := Nat.mul_le_mul secondLength (by omega)
              have inner : second.length*(first.length+second.length+1)+first.length+second.length+2 ≤
                  input.length*(input.length+1)+input.length+2 := by omega
              have outer := Nat.mul_le_mul secondLength inner
              simp only [Nat.mul_assoc] at *
              omega
            exact bounded.trans (larger.trans (by nlinarith))
          · simp only [productPayload,firstParsed,secondParsed]
            simpa only [split,splitSecond,List.append_assoc] using executed

theorem productPayload_length (input : List Bool) : (productPayload input).length ≤ (input.length+1)^2 := by
  unfold productPayload
  cases firstParsed : Encoding.unframe input with
  | none => simp
  | some pair =>
      obtain ⟨first,rest⟩ := pair
      cases secondParsed : Encoding.unframe rest with
      | none => simp only [secondParsed,List.length_nil,Nat.zero_le]
      | some pair =>
          obtain ⟨second,suffix⟩ := pair
          have split := Machine.unframe_sound input first rest firstParsed
          have splitSecond := Machine.unframe_sound rest second suffix secondParsed
          have length : first.length+second.length ≤ input.length := by
            rw [split,splitSecond,List.length_append,List.length_append,Encoding.frame_length,Encoding.frame_length]
            omega
          simp only [secondParsed]
          have bounded := multiplyBits_length first second
          have larger : second.length*(first.length+second.length+1) ≤ input.length*(input.length+1) := by
            apply Nat.mul_le_mul <;> omega
          exact bounded.trans (larger.trans (by nlinarith))

theorem productFunction_natural (first second : Nat) :
    productFunction ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) =
      Encoding.natural.encode (first*second) := by
  change Encoding.natural.encode (Encoding.value (productPayload
    (Encoding.frame first.bits++Encoding.frame second.bits))) = _
  simp only [productPayload,Encoding.unframe_frame]
  have secondDecoded : Encoding.unframe (Encoding.frame second.bits)=some (second.bits,[]) := by
    simpa only [List.append_nil] using Encoding.unframe_frame second.bits []
  simp only [secondDecoded]
  rw [multiplyBits_value,Encoding.value_bits,Encoding.value_bits]

end Counting.StackMachine.Binary
