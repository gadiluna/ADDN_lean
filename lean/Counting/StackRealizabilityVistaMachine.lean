import Counting.StackRealizabilityVistaEntry
import Counting.StackCompilerComplete
import Counting.ComplexityBooleanVerifier

namespace Counting.StackMachine.VistaComplement
open Routine
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifier_computes : ComputesIn verifier.program (fun input=>[predicate input])
    (Complexity.polynomial verifierCoefficient 25) := by
  intro input
  obtain ⟨time,bound,result,execution,answer⟩ := verifier_executes input
  obtain ⟨finish,run,halt,store⟩ := execution
  exact ⟨time,finish,bound,⟨run,halt⟩,store ▸ answer⟩

def machine : Machine.Program := Compiler.compile verifier.program

def machineCoefficient : Nat := 20*(verifierCoefficient+133)^2

/-- Total physical running time includes canonical syntax checking, two
calls to the compact realizability verifier, order inequality and cleanup. -/
theorem machine_computes : Complexity.ComputesCleanIn machine (fun input=>[predicate input])
    (Complexity.polynomial machineCoefficient 52) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 25 verifier_computes

/-- Malformed view inputs have empty spectrum, exactly as in the paper's
recognition convention. The witness bound is in the actual binary input. -/
theorem BinaryAtMostOneVista_in_coNP : Complexity.coNP Encoding.BinaryAtMostOneVista := by
  apply machine_computes.conp_of_bounded_counterexamples
    (witnessCoefficient:=20) (witnessExponent:=3)
  intro input
  change (¬ Encoding.BinaryAtMostOneVista input) ↔ _
  simpa only [predicate_pairWords,Complexity.polynomial] using Encoding.binaryVista_complement_iff input

end Counting.StackMachine.VistaComplement
