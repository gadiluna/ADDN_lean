import Counting.StackVistaFirst
import Counting.StackCompilerComplete
import Counting.HardnessVistaRawReduction
import Counting.DagRawArray

namespace Counting.Machine
open StackMachine.VistaFirst
set_option maxHeartbeats 1500000

def vistaFirstProgram : Program := StackMachine.Compiler.compile complete.program

/-- Every stack step, tape simulation step and final cleanup is charged.
The precondition concerns the typed configuration supplied by reconstruction. -/
theorem vistaFirst_clean (first : Executable.Vista) (rest : List Executable.Vista) :
    ∃ time output,
      time ≤ 20*(12000+23)^2*((inputWord first rest).length+1)^8 ∧
      HaltsAt vistaFirstProgram (inputWord first rest) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((outputWord first).map bitSymbol) := by
  obtain ⟨steps, bounded, last, ran, halted, stored⟩ := complete_executes first rest
  have stackHalt : StackMachine.HaltsAt complete.program (inputWord first rest) steps last := ⟨ran, halted⟩
  obtain ⟨time, output, timeBound, execution, tape⟩ := StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time, output, timeBound.trans ?_, execution, ?_⟩
  · let N := (inputWord first rest).length
    have linear : N+1 ≤ (N+1)^4 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (N+1)^4 := Nat.one_le_pow' 4 N
    have base : N+18+steps+4 ≤ (12000+23)*(N+1)^4 := by
      change steps ≤ 12000*(N+1)^4 at bounded
      omega
    calc
      _ ≤ 20*((12000+23)*(N+1)^4)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by dsimp [N]; ring
  · rw [stored] at tape
    exact tape

theorem vistaFirst_raw_input (input : Simulation.Input) (nonempty : 0 < input.leaders.size) :
    ∃ time output,
      time ≤ 20*(12000+23)^2*(((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)).length+1)^8 ∧
      HaltsAt vistaFirstProgram ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((HardnessVistaRaw.firstWord input).map bitSymbol) := by
  have nonemptyViews : (Encoding.rawInputVistas input).toList ≠ [] := by
    intro empty
    have size := congrArg List.length empty
    simp only [Array.length_toList, Encoding.rawInputVistas_size, List.length_nil] at size
    omega
  obtain ⟨first, rest, same⟩ := List.exists_cons_of_ne_nil nonemptyViews
  have code : ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)) = inputWord first rest := by
    change (Encoding.list Encoding.vista).encode (Encoding.rawInputVistas input).toList = _
    rw [same]
    rfl
  have output : HardnessVistaRaw.firstWord input = outputWord first := by
    unfold HardnessVistaRaw.firstWord
    rw [←Array.getElem?_toList, same]
    rfl
  simpa only [code, output] using vistaFirst_clean first rest

theorem vistaFirst_raw_input_polynomial (input : Simulation.Input) (nonempty : 0 < input.leaders.size) :
    ∃ time output,
      time ≤ (20*(12000+23)^2*204^8)*((Encoding.networkInput.encode input).length+1)^48 ∧
      HaltsAt vistaFirstProgram ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((HardnessVistaRaw.firstWord input).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := vistaFirst_raw_input input nonempty
  have encoded := Encoding.rawInputVistas_array_encoding_length input
  have positive : 1 ≤ ((Encoding.networkInput.encode input).length+1)^6 := Nat.one_le_pow' 6 _
  have base : ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)).length+1 ≤
      204*((Encoding.networkInput.encode input).length+1)^6 := by omega
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  calc
    _ ≤ 20*(12000+23)^2*(204*((Encoding.networkInput.encode input).length+1)^6)^8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 8)
    _ = _ := by ring

end Counting.Machine
