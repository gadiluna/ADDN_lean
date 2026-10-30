import Counting.StackBinaryDivisionParse
import Counting.StackBinaryMultiplyOutput

namespace Counting.StackMachine.Binary.Division
open Routine EncodingPrograms

abbrev zeroTest : Routine 8 := ofProgram (compareProgram 7 2 7 5)
abbrev zeroChoice : Routine 8 := branchRoutine 5 (clear 1) (skip 8)
abbrev guardZero : Routine 8 := sequence zeroTest zeroChoice
abbrev formatOutput : Routine 8 := Normalize.formatRoutine 7 1 6 8
abbrev copyOutput : Routine 8 := ofProgram (ListPrograms.copyProgram 7 6 1 8)
abbrev finishOutput : Routine 8 := sequence formatOutput copyOutput
abbrev outputRoutine : Routine 8 := sequence guardZero finishOutput
abbrev divisionRoutine : Routine 8 := sequence parsedDivision outputRoutine

def zeroAdjusted (divisor quotient : List Bool) : List Bool :=
  if compareBits true divisor [] then [] else quotient

theorem zeroAdjusted_length (divisor quotient : List Bool) :
    (zeroAdjusted divisor quotient).length ≤ quotient.length := by
  unfold zeroAdjusted
  split_ifs <;> simp

theorem guard_executes (input quotient divisor remainder : List Bool) :
    ∃ transitions ≤ 2*divisor.length+quotient.length+6,
      Executes guardZero (file input quotient divisor remainder [] [] [] [] [] []) transitions
        (file input (zeroAdjusted divisor quotient) [] remainder [] [] [] [] [] []) := by
  have compared := binary_compare_executes 7 2 7 5 (by decide) (by decide) (by decide)
    (file input quotient divisor remainder [] [] [] [] [] [])
  change Executes zeroTest (file input quotient divisor remainder [] [] [] [] [] [])
    (2*max divisor.length 0+3)
    (Function.update (Function.update (Function.update (file input quotient divisor remainder [] [] [] [] [] []) 2 []) 7 []) 5
      [compareBits true divisor []]) at compared
  have comparedStore : Function.update (Function.update (Function.update (file input quotient divisor remainder [] [] [] [] [] []) 2 []) 7 []) 5
      [compareBits true divisor []] = file input quotient [] remainder [] [compareBits true divisor []] [] [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [comparedStore,Nat.max_zero] at compared
  have cleaned (flag : Bool) : Function.update (file input quotient [] remainder [] [flag] [] [] [] []) 5 [] =
      file input quotient [] remainder [] [] [] [] [] [] := by
    funext r
    fin_cases r <;> rfl
  by_cases zero : compareBits true divisor [] = true
  · have cleared := clear_executes (registers := 8) 1 (file input quotient [] remainder [] [] [] [] [] [])
    change Executes (clear 1) (file input quotient [] remainder [] [] [] [] [] []) (quotient.length+1)
      (Function.update (file input quotient [] remainder [] [] [] [] [] []) 1 []) at cleared
    have clearedStore : Function.update (file input quotient [] remainder [] [] [] [] [] []) 1 [] =
        file input [] [] remainder [] [] [] [] [] [] := by
      funext r
      fin_cases r <;> rfl
    rw [clearedStore] at cleared
    have chosen := branch_executes_true 5 (clear 1) (skip 8)
      (file input quotient [] remainder [] [true] [] [] [] []) (file input [] [] remainder [] [] [] [] [] []) []
      (quotient.length+1) rfl (by rw [cleaned]; exact cleared)
    rw [zero] at compared
    refine ⟨_,?_,by simpa only [zeroAdjusted,zero,ite_true] using compared.sequence chosen⟩
    omega
  · have notZero : compareBits true divisor [] = false := Bool.eq_false_iff.mpr zero
    have chosen := branch_executes_false 5 (clear 1) (skip 8)
      (file input quotient [] remainder [] [false] [] [] [] []) (file input quotient [] remainder [] [] [] [] [] []) [] 0 rfl
      (by rw [cleaned]; exact skip_executes _)
    rw [notZero] at compared
    refine ⟨_,?_,by simpa only [zeroAdjusted,notZero,Bool.false_eq_true,ite_false] using compared.sequence chosen⟩
    omega

theorem finish_executes (input payload remainder : List Bool) :
    ∃ transitions ≤ 15*payload.length+12,
      Executes finishOutput (file input payload [] remainder [] [] [] [] [] []) transitions
        (file input (Encoding.natural.encode (Encoding.value payload)) [] remainder [] []
          (Encoding.natural.encode (Encoding.value payload)) [] [] []) := by
  let encoded := Encoding.natural.encode (Encoding.value payload)
  have formatted := Normalize.format_executes 7 1 6 8 (by decide) (by decide) (by decide)
    (file input payload [] remainder [] [] [] [] [] []) rfl
  change Executes formatOutput (file input payload [] remainder [] [] [] [] [] []) (Normalize.formatCost payload)
    (Function.update (Function.update (file input payload [] remainder [] [] [] [] [] []) 1 []) 6 (encoded++[])) at formatted
  have formattedStore : Function.update (Function.update (file input payload [] remainder [] [] [] [] [] []) 1 []) 6 (encoded++[]) =
      file input [] [] remainder [] [] encoded [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [formattedStore] at formatted
  have copied := copy_executes 7 6 1 8 (by decide) (by decide) (by decide)
    (file input [] [] remainder [] [] encoded [] [] []) rfl
  change Executes copyOutput (file input [] [] remainder [] [] encoded [] [] []) (5*encoded.length+2)
    (Function.update (file input [] [] remainder [] [] encoded [] [] []) 1 (encoded++[])) at copied
  have copiedStore : Function.update (file input [] [] remainder [] [] encoded [] [] []) 1 (encoded++[]) =
      file input encoded [] remainder [] [] encoded [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [copiedStore] at copied
  refine ⟨_,?_,formatted.sequence copied⟩
  have formatBound := Normalize.formatCost_le payload
  have outputBound := natural_value_length payload
  change encoded.length ≤ 2*payload.length+1 at outputBound
  omega

def quotientFunction (input : List Bool) : List Bool :=
  let parsed := parsePair input
  Encoding.natural.encode (Encoding.value parsed.first / Encoding.value parsed.second)

theorem adjusted_quotient (dividend divisor : List Bool) :
    Encoding.value (zeroAdjusted divisor (divideBits dividend divisor).1) =
      Encoding.value dividend / Encoding.value divisor := by
  have zeroSpec := compareBits_le divisor []
  simp only [Encoding.value,Nat.le_zero] at zeroSpec
  by_cases zero : compareBits true divisor [] = true
  · rw [zeroAdjusted,if_pos zero,zeroSpec.mp zero]
    simp [Encoding.value]
  · rw [zeroAdjusted,if_neg zero]
    exact (divideBits_correct dividend divisor (by
      have nonzero : Encoding.value divisor ≠ 0 := fun h => zero (zeroSpec.mpr h)
      omega)).1

/-- Total quotient computation on the sequential natural-pair format.
Incomplete input is assigned zero, as is division by zero. -/
theorem division_computes : ComputesIn divisionRoutine.program quotientFunction (Complexity.polynomial 180 2) := by
  intro input
  let parsed := parsePair input
  let divided := divideBits parsed.first parsed.second
  obtain ⟨parseTime,parseBound,parsedRun⟩ := parsed_division_executes input
  obtain ⟨guardTime,guardBound,guarded⟩ := guard_executes parsed.suffix divided.1 parsed.second divided.2
  obtain ⟨finishTime,finishBound,finished⟩ := finish_executes parsed.suffix (zeroAdjusted parsed.second divided.1) divided.2
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (guarded.sequence finished)
  refine ⟨parseTime+1+(guardTime+1+finishTime),finish,?_,⟨?_,halted⟩,?_⟩
  · have payloadBound := zeroAdjusted_length parsed.second divided.1
    have quotientLength : divided.1.length = parsed.first.length := by
      change (divideAcc parsed.first.reverse parsed.second [] []).1.length = parsed.first.length
      rw [divideAcc_quotient_length,List.length_reverse,List.length_nil,Nat.add_zero]
    have lengths := parsePair_length_bound input
    change parsed.first.length+parsed.second.length+parsed.suffix.length ≤ input.length at lengths
    rw [quotientLength] at guardBound payloadBound
    change parseTime+1+(guardTime+1+finishTime) ≤ 180*(input.length+1)^2
    nlinarith
  · have start : initial divisionRoutine.program input = ⟨0,file input [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.natural.encode (Encoding.value (zeroAdjusted parsed.second (divideBits parsed.first parsed.second).1)) = _
    rw [adjusted_quotient]
    rfl

theorem quotientFunction_natural (first second : Nat) :
    quotientFunction ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) =
      Encoding.natural.encode (first/second) := by
  have parsed := parsePair_frames first.bits second.bits []
  simp only [List.append_nil] at parsed
  change Encoding.natural.encode (Encoding.value (parsePair (Encoding.frame first.bits++Encoding.frame second.bits)).first /
    Encoding.value (parsePair (Encoding.frame first.bits++Encoding.frame second.bits)).second) = _
  rw [parsed,Encoding.value_bits,Encoding.value_bits]

end Counting.StackMachine.Binary.Division
