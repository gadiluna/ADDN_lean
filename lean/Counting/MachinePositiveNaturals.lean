import Counting.StackPositiveNaturals
import Counting.StackCompilerComplete
import Counting.EncodingNetwork

namespace Counting.PositiveNaturals

theorem output_executable (row : List Rat) : output row =
    (Encoding.optional (Encoding.array Encoding.natural)).encode (Executable.positiveNaturals? row.toArray) := by
  rw [result_executable]
  unfold output
  cases result row <;> simp [Encoding.optional,Encoding.array,Encoding.transport]

end Counting.PositiveNaturals

namespace Counting.Machine
open StackMachine.PositiveNaturals

def positiveNaturalsProgram : Program := StackMachine.Compiler.compile complete.program

/-- On canonical encoded vectors the actual machine returns exactly the
optional array returned by the solver's positivity/integrality conversion.
The bound includes parsing, every scalar call, both outcome paths and cleanup. -/
theorem positiveNaturals_clean (row : List Rat) :
    ∃ time output,
      time ≤ (20*10035^2)*((Encoding.rationalRow.encode row).length+1)^6 ∧
      HaltsAt positiveNaturalsProgram (Encoding.rationalRow.encode row) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional (Encoding.array Encoding.natural)).encode
          (Executable.positiveNaturals? row.toArray)).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts row
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (Encoding.rationalRow.encode row).length
    change 20*(size+30+steps+4)^2 ≤ (20*10035^2)*(size+1)^6
    have linear : size+1 ≤ (size+1)^3 := Nat.le_self_pow (by decide) _
    have positive := Nat.one_le_pow' 3 size
    have base : size+30+steps+4 ≤ 10035*(size+1)^3 := by
      change steps ≤ 10000*(size+1)^3 at bounded
      omega
    calc
      _ ≤ 20*(10035*(size+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored,Counting.PositiveNaturals.output_executable] at tape
    exact tape

theorem positiveNaturals_array_clean (vector : Array Rat) :
    ∃ time output,
      time ≤ (20*10035^2)*((Encoding.rationalRow.encode vector.toList).length+1)^6 ∧
      HaltsAt positiveNaturalsProgram (Encoding.rationalRow.encode vector.toList) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional (Encoding.array Encoding.natural)).encode
          (Executable.positiveNaturals? vector)).map bitSymbol) := by
  simpa using positiveNaturals_clean vector.toList

end Counting.Machine
