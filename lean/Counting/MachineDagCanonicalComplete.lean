import Counting.StackDagCanonicalComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.DagUpdate.Canonical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option exponentiation.threshold 1024

def canonicalDagProgram : Program := StackMachine.Compiler.compile completeCanonical.program
def canonicalDagCoefficient : Nat := 20*(completeCanonicalCoefficient+133)^2

/-- The exact executable canonical DAG is computed by a finite-alphabet
machine, with clean output and polynomial physical transition count. -/
theorem canonicalDag_clean (source : Executable.Vista) (valid : Executable.NodesValid source)
    (nonempty : 0 < source.nodes.size) :
    ∃ time output,
      time ≤ canonicalDagCoefficient*((Encoding.vista.encode source).length+1)^272 ∧
      HaltsAt canonicalDagProgram (Encoding.vista.encode source) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.vista.encode (Executable.canonicalize source)).map bitSymbol) := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩ := completeCanonical_executes source valid nonempty
  have stackHalt : StackMachine.HaltsAt completeCanonical.program (Encoding.vista.encode source) steps last := ⟨ran,halted⟩
  obtain ⟨time,output,cost,execution,tape⟩ := StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,cost.trans ?_,execution,?_⟩
  · let N := (Encoding.vista.encode source).length
    have linear : N+1 ≤ (N+1)^136 := Nat.le_self_pow (by decide) _
    have one : 1 ≤ (N+1)^136 := Nat.one_le_pow' _ _
    have base : N+128+steps+4 ≤ (completeCanonicalCoefficient+133)*(N+1)^136 := by
      change steps ≤ completeCanonicalCoefficient*(N+1)^136 at bounded
      rw [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeCanonicalCoefficient+133)*(N+1)^136)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by
        rw [Nat.mul_pow,←Nat.pow_mul]
        change 20*((completeCanonicalCoefficient+133)^2*(N+1)^272)=canonicalDagCoefficient*(N+1)^272
        exact (Nat.mul_assoc 20 ((completeCanonicalCoefficient+133)^2) ((N+1)^272)).symm
  · rw [stored] at tape
    exact tape

end Counting.Machine
