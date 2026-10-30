import Counting.NetworkVistaRunComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.NetworkVista.Run
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

def networkVistaRawProgram : Program := StackMachine.Compiler.compile complete.program
def networkVistaRawCoefficient : Nat := 20*(completeCoefficient+133)^2

/-- Actual finite-alphabet tape transitions, including bootstrap and full
cleanup, for offline reconstruction of all observers' physical histories. -/
theorem networkVistaRaw_clean (input : Simulation.Input) (valid : Encoding.networkValid input=true) :
    ∃ time output,
      time ≤ networkVistaRawCoefficient*((Encoding.networkInput.encode input).length+1)^746 ∧
      HaltsAt networkVistaRawProgram (Encoding.networkInput.encode input) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        (((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)).map bitSymbol) := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩ := complete_executes input valid
  have stackHalt : StackMachine.HaltsAt complete.program (Encoding.networkInput.encode input) steps last := ⟨ran,halted⟩
  obtain ⟨time,output,cost,execution,tape⟩ := StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,cost.trans ?_,execution,?_⟩
  · let N := (Encoding.networkInput.encode input).length
    have linear : N+1≤(N+1)^373 := Nat.le_self_pow (by decide) _
    have one : 1≤(N+1)^373 := Nat.one_le_pow' _ _
    have base : N+128+steps+4≤(completeCoefficient+133)*(N+1)^373 := by
      change steps≤completeCoefficient*(N+1)^373 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeCoefficient+133)*(N+1)^373)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by
        rw [Nat.mul_pow,←Nat.pow_mul]
        change 20*((completeCoefficient+133)^2*(N+1)^746)=networkVistaRawCoefficient*(N+1)^746
        unfold networkVistaRawCoefficient
        exact (Nat.mul_assoc 20 ((completeCoefficient+133)^2) ((N+1)^746)).symm
  · rw [stored] at tape
    exact tape

end Counting.Machine
