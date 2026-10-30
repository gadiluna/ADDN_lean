import Counting.StackSignedOutput

namespace Counting.StackMachine.Signed
open Routine

abbrev signedAdditionRoutine : Routine 10 := sequence parsedAddition formatOutput

/-- Total signed addition: even incomplete input words halt in a linear
number of stack transitions. Completed operands are interpreted with their
sign; missing or truncated magnitudes denote zero. -/
theorem signedAddition_computes :
    ComputesIn signedAdditionRoutine.program signedAdditionFunction (Complexity.polynomial 100 1) := by
  intro input
  obtain ⟨parseTime,parseBound,parsed⟩ := parsed_addition_executes input
  obtain ⟨formatTime,formatBound,formatted⟩ := formatOutput_executes
    (parsedSuffix input) (sumPayload input).2 (sumPayload input).1
  obtain ⟨finish,ran,halted,stored⟩ := parsed.sequence formatted
  refine ⟨parseTime+1+formatTime,finish,?_,⟨?_,halted⟩,?_⟩
  · have length := sumPayload_length input
    change parseTime+1+formatTime ≤ 100*(input.length+1)^1
    rw [pow_one]
    omega
  · have start : initial signedAdditionRoutine.program input = ⟨0,file input [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (value (sumPayload input).1 (sumPayload input).2) = _
    rw [sumPayload_value]
    rfl

end Counting.StackMachine.Signed
