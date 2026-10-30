import Counting.StackNetworkComplementTotal
import Counting.StackCompilerComplete
import Counting.ComplexityBooleanVerifier

namespace Counting.StackMachine.NetworkComplement
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 2000000

theorem verifier_computes : ComputesIn verifier.program (fun input=>[predicate input])
    (Complexity.polynomial verifierCoefficient 373) := by
  intro input
  obtain ⟨time,bound,result,execution,answer⟩ := verifier_executes input
  obtain ⟨finish,run,halt,store⟩ := execution
  exact ⟨time,finish,bound,⟨run,halt⟩,store ▸ answer⟩

def machine : Machine.Program := Compiler.compile verifier.program
def machineCoefficient : Nat := 20*(verifierCoefficient+163)^2

/-- An unconditional finite-alphabet physical Turing computation of the
full network complement verifier, including malformed binary inputs. -/
theorem machine_computes : Complexity.ComputesCleanIn machine (fun input=>[predicate input])
    (Complexity.polynomial machineCoefficient 748) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 373 verifier_computes

/-- The exact binary language of the manuscript belongs to coNP. Every
algorithmic ingredient and the bit-time simulation are instantiated above. -/
theorem BinarySomeAgentKnows_in_coNP : Complexity.coNP Encoding.BinarySomeAgentKnows := by
  apply machine_computes.conp_of_bounded_counterexamples
    (witnessCoefficient:=20*204^3+3) (witnessExponent:=16)
  intro input
  change (¬ Encoding.BinarySomeAgentKnows input) ↔ _
  simpa only [predicate_pairWords,Complexity.polynomial] using
    Counting.NetworkCertificate.binaryRawNetwork_complement_iff input

end Counting.StackMachine.NetworkComplement
