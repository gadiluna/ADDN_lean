import Counting.StackBinaryGcdBody
import Counting.StackRoutineUnary

namespace Counting.StackMachine.Binary.Gcd
open Routine EncodingPrograms

abbrev normalizeFirst : Routine 8 := normalizePayload 7 6 7 8
abbrev normalizeSecond : Routine 8 := normalizePayload 7 2 7 8
abbrev countLength : Routine 8 := ofProgram (Unary.lengthProgram 7 2 0 8)
abbrev countTwice : Routine 8 := sequence countLength (sequence countLength (pushBit 0 true))
abbrev initialization : Routine 8 := sequence Division.parser
  (sequence (clear 5) (sequence (clear 0) (sequence normalizeFirst (sequence normalizeSecond countTwice))))

theorem count_executes (first second : Nat) :
    Executes countTwice (file [] first second) (10*second.size+7)
      (file (List.replicate (2*second.size+1) true) first second) := by
  have count (counter : List Bool) : Executes countLength (file counter first second) (5*second.size+2)
      (file (List.replicate second.size true++counter) first second) := by
    have counted := length_executes 7 2 0 8 (by decide) (by decide) (by decide) (file counter first second) rfl
    change Executes countLength (file counter first second) (5*second.bits.length+2)
      (Function.update (file counter first second) 0 (List.replicate second.bits.length true++counter)) at counted
    rw [Encoding.bits_length] at counted
    have changed : Function.update (file counter first second) 0 (List.replicate second.size true++counter) =
        file (List.replicate second.size true++counter) first second := by
      funext r
      fin_cases r <;> rfl
    rw [changed] at counted
    exact counted
  have firstRun := count []
  simp only [List.append_nil] at firstRun
  have secondRun := count (List.replicate second.size true)
  have pushed := pushBit_executes (registers := 8) 0 true
    (file (List.replicate second.size true++List.replicate second.size true) first second)
  have result : Function.update (file (List.replicate second.size true++List.replicate second.size true) first second) 0
      (true::(file (List.replicate second.size true++List.replicate second.size true) first second) 0) =
      file (List.replicate (2*second.size+1) true) first second := by
    funext r
    fin_cases r <;> simp [file,Division.file,List.replicate_succ,two_mul]
  rw [result] at pushed
  have composed := firstRun.sequence (secondRun.sequence pushed)
  simpa only [show (5*second.size+2)+1+((5*second.size+2)+1+1)=10*second.size+7 by omega] using composed

theorem initialize_executes (input : List Bool) :
    ∃ transitions ≤ 50*(input.length+1),
      Executes initialization (Division.file input [] [] [] [] [] [] [] [] []) transitions
        (file (List.replicate (2*(Encoding.value (parsePair input).second).size+1) true)
          (Encoding.value (parsePair input).first) (Encoding.value (parsePair input).second)) := by
  let parsed := parsePair input
  obtain ⟨parseTime,parseBound,parsedRun⟩ := pair_executes_spec 5 Division.parseRoles Division.parseRoles_injective
    (Division.file input [] [] [] [] [] [] [] [] []) rfl
  have parsedStore : pairExpected 5 Division.parseRoles (Division.file input [] [] [] [] [] [] [] [] []) =
      Division.file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] [] := by
    funext r
    fin_cases r <;> simp [pairExpected,Division.parseRoles,Division.file,parsed]
  rw [parsedStore] at parsedRun
  have clearedFlag := clear_executes (registers := 8) 5
    (Division.file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] [])
  change Executes (clear 5) (Division.file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 2
    (Function.update (Division.file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 5 []) at clearedFlag
  have noFlag : Function.update (Division.file parsed.suffix [] parsed.second [] [] [parsed.accepted] parsed.first [] [] []) 5 [] =
      Division.file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [noFlag] at clearedFlag
  have clearedInput := clear_executes (registers := 8) 0
    (Division.file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] [])
  change Executes (clear 0) (Division.file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] []) (parsed.suffix.length+1)
    (Function.update (Division.file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] []) 0 []) at clearedInput
  have noInput : Function.update (Division.file parsed.suffix [] parsed.second [] [] [] parsed.first [] [] []) 0 [] =
      Division.file [] [] parsed.second [] [] [] parsed.first [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [noInput] at clearedInput
  have firstRun := normalizePayload_executes 7 6 7 8 (by decide) (by decide) (by decide)
    (Division.file [] [] parsed.second [] [] [] parsed.first [] [] []) rfl rfl
  change Executes normalizeFirst (Division.file [] [] parsed.second [] [] [] parsed.first [] [] [])
    (normalizePayloadCost parsed.first)
    (Function.update (Division.file [] [] parsed.second [] [] [] parsed.first [] [] []) 6 (Encoding.value parsed.first).bits) at firstRun
  have firstStore : Function.update (Division.file [] [] parsed.second [] [] [] parsed.first [] [] []) 6 (Encoding.value parsed.first).bits =
      Division.file [] [] parsed.second [] [] [] (Encoding.value parsed.first).bits [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [firstStore] at firstRun
  have secondRun := normalizePayload_executes 7 2 7 8 (by decide) (by decide) (by decide)
    (Division.file [] [] parsed.second [] [] [] (Encoding.value parsed.first).bits [] [] []) rfl rfl
  change Executes normalizeSecond (Division.file [] [] parsed.second [] [] [] (Encoding.value parsed.first).bits [] [] [])
    (normalizePayloadCost parsed.second)
    (Function.update (Division.file [] [] parsed.second [] [] [] (Encoding.value parsed.first).bits [] [] []) 2 (Encoding.value parsed.second).bits) at secondRun
  have secondStore : Function.update (Division.file [] [] parsed.second [] [] [] (Encoding.value parsed.first).bits [] [] []) 2 (Encoding.value parsed.second).bits =
      file [] (Encoding.value parsed.first) (Encoding.value parsed.second) := by
    funext r
    fin_cases r <;> rfl
  rw [secondStore] at secondRun
  have counted := count_executes (Encoding.value parsed.first) (Encoding.value parsed.second)
  refine ⟨_,?_,parsedRun.sequence (clearedFlag.sequence (clearedInput.sequence (firstRun.sequence (secondRun.sequence counted))))⟩
  have firstBound := normalizePayloadCost_le parsed.first
  have secondBound := normalizePayloadCost_le parsed.second
  have sizeBound := normalize_length_le parsed.second
  rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at sizeBound
  have lengths := parsePair_length_bound input
  change parsed.first.length+parsed.second.length+parsed.suffix.length ≤ input.length at lengths
  change parseTime ≤ 6*input.length+13 at parseBound
  omega

end Counting.StackMachine.Binary.Gcd
