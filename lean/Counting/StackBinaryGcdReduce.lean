import Counting.StackBinaryDivisionParse
import Counting.StackBinaryNormalize
import Counting.StackRoutineMove

namespace Counting.StackMachine.Binary.Gcd
open Routine

abbrev rawDivision : Routine 8 := sequence Division.reverseInput Division.routine
abbrev moveDivisor : Routine 8 := move 7 2 6 8
abbrev normalizeRemainder : Routine 8 := normalizePayload 7 3 7 8
abbrev moveRemainder : Routine 8 := move 7 3 2 8
abbrev reset : Routine 8 := sequence (clear 1) (sequence moveDivisor (sequence normalizeRemainder moveRemainder))
abbrev reduce : Routine 8 := sequence rawDivision reset

def file (counter : List Bool) (first second : Nat) : Fin 10 → List Bool :=
  Division.file counter [] second.bits [] [] [] first.bits [] [] []

theorem raw_executes (counter first second : List Bool) :
    ∃ transitions ≤ 2*first.length+2+(34*first.length*(2*second.length+first.length+2)+1),
      Executes rawDivision (Division.file counter [] second [] [] [] first [] [] []) transitions
        (Division.file counter (divideBits first second).1 second (divideBits first second).2 [] [] [] [] [] []) := by
  have reversed := reverse_executes 8 6 4 (by decide) (Division.file counter [] second [] [] [] first [] [] [])
  change Executes Division.reverseInput (Division.file counter [] second [] [] [] first [] [] []) (2*first.length+1)
    (Function.update (Function.update (Division.file counter [] second [] [] [] first [] [] []) 6 []) 4 (first.reverse++[])) at reversed
  have changed : Function.update (Function.update (Division.file counter [] second [] [] [] first [] [] []) 6 []) 4 (first.reverse++[]) =
      Division.file counter [] second [] first.reverse [] [] [] [] [] := by
    funext r
    fin_cases r <;> simp [Division.file]
  rw [changed] at reversed
  obtain ⟨time,bounded,executed⟩ := Division.divide_payloads counter first second
  exact ⟨(2*first.length+1)+1+time,by omega,reversed.sequence executed⟩

theorem reset_executes (counter quotient divisor remainder : List Bool) :
    ∃ transitions ≤ quotient.length+6*divisor.length+16*remainder.length+19,
      Executes reset (Division.file counter quotient divisor remainder [] [] [] [] [] []) transitions
        (Division.file counter [] (Encoding.value remainder).bits [] [] [] divisor [] [] []) := by
  have cleared := clear_executes (registers := 8) 1 (Division.file counter quotient divisor remainder [] [] [] [] [] [])
  change Executes (clear 1) (Division.file counter quotient divisor remainder [] [] [] [] [] []) (quotient.length+1)
    (Function.update (Division.file counter quotient divisor remainder [] [] [] [] [] []) 1 []) at cleared
  have clearStore : Function.update (Division.file counter quotient divisor remainder [] [] [] [] [] []) 1 [] =
      Division.file counter [] divisor remainder [] [] [] [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [clearStore] at cleared
  have moved := move_executes 7 2 6 8 (by decide) (by decide) (by decide)
    (Division.file counter [] divisor remainder [] [] [] [] [] []) rfl
  change Executes moveDivisor (Division.file counter [] divisor remainder [] [] [] [] [] []) (6*divisor.length+4)
    (Function.update (Function.update (Division.file counter [] divisor remainder [] [] [] [] [] []) 6 (divisor++[])) 2 []) at moved
  have moveStore : Function.update (Function.update (Division.file counter [] divisor remainder [] [] [] [] [] []) 6 (divisor++[])) 2 [] =
      Division.file counter [] [] remainder [] [] divisor [] [] [] := by
    funext r
    fin_cases r <;> simp [Division.file]
  rw [moveStore] at moved
  have normalized := normalizePayload_executes 7 3 7 8 (by decide) (by decide) (by decide)
    (Division.file counter [] [] remainder [] [] divisor [] [] []) rfl rfl
  change Executes normalizeRemainder (Division.file counter [] [] remainder [] [] divisor [] [] []) (normalizePayloadCost remainder)
    (Function.update (Division.file counter [] [] remainder [] [] divisor [] [] []) 3 (Encoding.value remainder).bits) at normalized
  have normStore : Function.update (Division.file counter [] [] remainder [] [] divisor [] [] []) 3 (Encoding.value remainder).bits =
      Division.file counter [] [] (Encoding.value remainder).bits [] [] divisor [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [normStore] at normalized
  have restored := move_executes 7 3 2 8 (by decide) (by decide) (by decide)
    (Division.file counter [] [] (Encoding.value remainder).bits [] [] divisor [] [] []) rfl
  change Executes moveRemainder (Division.file counter [] [] (Encoding.value remainder).bits [] [] divisor [] [] [])
    (6*(Encoding.value remainder).bits.length+4)
    (Function.update (Function.update (Division.file counter [] [] (Encoding.value remainder).bits [] [] divisor [] [] []) 2
      ((Encoding.value remainder).bits++[])) 3 []) at restored
  have restoreStore : Function.update (Function.update (Division.file counter [] [] (Encoding.value remainder).bits [] [] divisor [] [] []) 2
      ((Encoding.value remainder).bits++[])) 3 [] =
      Division.file counter [] (Encoding.value remainder).bits [] [] [] divisor [] [] [] := by
    funext r
    fin_cases r <;> simp [Division.file]
  rw [restoreStore] at restored
  refine ⟨_,?_,cleared.sequence (moved.sequence (normalized.sequence restored))⟩
  have normalizedBound := normalizePayloadCost_le remainder
  have lengthBound := EncodingPrograms.normalize_length_le remainder
  rw [Arithmetic.normalize_eq_bits] at lengthBound
  omega

/-- One physical Euclidean reduction, with all loop scratch restored. -/
theorem reduce_executes (counter : List Bool) (first second : Nat) (positive : 0 < second) :
    ∃ transitions ≤ 200*(first.size+second.size+1)^2,
      Executes reduce (file counter first second) transitions (file counter second (first%second)) := by
  obtain ⟨divideTime,divideBound,divided⟩ := raw_executes counter first.bits second.bits
  obtain ⟨resetTime,resetBound,resetRun⟩ := reset_executes counter (divideBits first.bits second.bits).1
    second.bits (divideBits first.bits second.bits).2
  have correct := divideBits_correct first.bits second.bits (by simpa only [Encoding.value_bits] using positive)
  simp only [Encoding.value_bits] at correct
  rw [correct.2] at resetRun
  refine ⟨divideTime+1+resetTime,?_,divided.sequence resetRun⟩
  have quotientLength : (divideBits first.bits second.bits).1.length = first.size := by
    change (divideAcc first.bits.reverse second.bits [] []).1.length = first.size
    rw [divideAcc_quotient_length,List.length_reverse,List.length_nil,Nat.add_zero,Encoding.bits_length]
  have remainderLength : (divideBits first.bits second.bits).2.length ≤ second.size+first.size := by
    simpa only [divideBits,List.length_reverse,List.length_nil,Nat.max_zero,Encoding.bits_length] using
      divideAcc_remainder_length first.bits.reverse second.bits [] []
  rw [quotientLength,Encoding.bits_length] at resetBound
  simp only [Encoding.bits_length] at divideBound
  nlinarith

end Counting.StackMachine.Binary.Gcd
