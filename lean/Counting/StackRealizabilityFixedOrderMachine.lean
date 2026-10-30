import Counting.StackRealizabilityFixedOrderEntry
import Counting.StackCompilerComplete
import Counting.ComplexityBooleanVerifier

namespace Counting.StackMachine.FixedOrderRecognition
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

/-- Total physical running time includes the canonical input and count
parsers, field assembly, the complete compact verifier and clean output. -/
theorem machine_computes : Complexity.ComputesCleanIn machine (fun input=>[predicate input])
    (Complexity.polynomial machineCoefficient 52) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 25 verifier_computes

/-- Fixed-order realizability has a binary witness of quadratic length;
invalid encodings are negative instances, with no promise on the input. -/
theorem BinaryFixedOrderRealizable_in_NP : Complexity.NP Encoding.BinaryFixedOrderRealizable := by
  apply machine_computes.np_of_bounded_witnesses
    (witnessCoefficient:=3) (witnessExponent:=2)
  intro input
  change Encoding.BinaryFixedOrderRealizable input ↔ _
  simpa only [predicate_pairWords,Complexity.polynomial] using Encoding.binaryFixedOrder_bounded_witnesses input

end Counting.StackMachine.FixedOrderRecognition
