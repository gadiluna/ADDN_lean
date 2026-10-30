import Counting.StackBinaryMultiplyTotal
import Counting.StackNormalize
import Counting.StackEncodingCanonical

/-! Canonical output and a total input-length bound for binary shift-add
multiplication. The two operands use the actual repository frame codec. -/
namespace Counting.StackMachine.Binary
open Routine

abbrev formatPart : Routine 5 := Normalize.formatRoutine 4 1 4 6
abbrev copyOutput : Routine 5 := ofProgram (ListPrograms.copyProgram 4 4 1 6)
abbrev finishPart : Routine 5 := sequence formatPart copyOutput
abbrev multiplicationRoutine : Routine 5 := sequence parsedMultiply finishPart

theorem natural_value_length (payload : List Bool) :
    (Encoding.natural.encode (Encoding.value payload)).length ≤ 2*payload.length+1 := by
  have shorter := EncodingPrograms.normalize_length_le payload
  rw [Arithmetic.normalize_eq_bits] at shorter
  change (Encoding.frame (Encoding.value payload).bits).length ≤ _
  rw [Encoding.frame_length]
  omega

theorem finish_executes (suffix payload shifted scratch : List Bool) :
    ∃ transitions ≤ 15*payload.length+12,
      Executes finishPart (file suffix payload shifted [] [] scratch []) transitions
        (file suffix (Encoding.natural.encode (Encoding.value payload)) shifted []
          (Encoding.natural.encode (Encoding.value payload)) scratch []) := by
  let output := Encoding.natural.encode (Encoding.value payload)
  have formatted := Normalize.format_executes 4 1 4 6 (by decide) (by decide) (by decide)
    (file suffix payload shifted [] [] scratch []) rfl
  change Executes formatPart (file suffix payload shifted [] [] scratch []) (Normalize.formatCost payload)
    (Function.update (Function.update (file suffix payload shifted [] [] scratch []) 1 []) 4 (output++[])) at formatted
  have afterFormat : Function.update (Function.update (file suffix payload shifted [] [] scratch []) 1 []) 4 (output++[]) =
      file suffix [] shifted [] output scratch [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [afterFormat] at formatted
  have copied := copy_executes 4 4 1 6 (by decide) (by decide) (by decide)
    (file suffix [] shifted [] output scratch []) rfl
  change Executes copyOutput (file suffix [] shifted [] output scratch []) (5*output.length+2)
    (Function.update (file suffix [] shifted [] output scratch []) 1 (output++[])) at copied
  have afterCopy : Function.update (file suffix [] shifted [] output scratch []) 1 (output++[]) =
      file suffix output shifted [] output scratch [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [afterCopy] at copied
  refine ⟨Normalize.formatCost payload+1+(5*output.length+2),?_,formatted.sequence copied⟩
  have formatBound := Normalize.formatCost_le payload
  have outputBound := natural_value_length payload
  change output.length ≤ 2*payload.length+1 at outputBound
  omega

/-- Both parsing failure paths halt, and valid operands are processed by
one shift-add iteration per multiplier bit, regardless of their values. -/
theorem multiplication_computes :
    ComputesIn multiplicationRoutine.program productFunction (Complexity.polynomial 100 3) := by
  intro input
  obtain ⟨parseTime,parseBound,suffix,shifted,scratch,parsed⟩ := parsed_multiply_total input
  obtain ⟨finishTime,finishBound,finished⟩ := finish_executes suffix (productPayload input) shifted scratch
  obtain ⟨output,ran,halted,stored⟩ := parsed.sequence finished
  refine ⟨parseTime+1+finishTime,output,?_,⟨?_,halted⟩,?_⟩
  · have payloadBound := productPayload_length input
    change parseTime+1+finishTime ≤ 100*(input.length+1)^3
    have squareCube : (input.length+1)^2 ≤ (input.length+1)^3 := by
      have h := Nat.mul_le_mul_left ((input.length+1)^2) (show 1 ≤ input.length+1 by omega)
      nlinarith
    have positive := Nat.one_le_pow' 3 input.length
    omega
  · have start : initial multiplicationRoutine.program input =
        ⟨0,file input [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r
      fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.Binary
