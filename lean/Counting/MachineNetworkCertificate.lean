import Counting.StackNetworkCertificateTotal
import Counting.StackCompilerComplete
import Counting.NetworkCertificateRaw

namespace Counting.StackMachine.NetworkCertificate
set_option maxRecDepth 200000

/-- Total physical verifier for an already reconstructed, explicitly listed
array of vistas and a same-length list of two-order certificates. Malformed
words and unequal list lengths reject through charged physical guards. -/
theorem verifier_computes : ComputesIn verifier.program
    (fun input=>[Counting.NetworkCertificate.predicate input])
    (Complexity.polynomial verifierCoefficient 27) := by
  intro input
  obtain ⟨time,bound,result,execution,answer⟩ := verifier_executes input
  obtain ⟨finish,run,halt,store⟩ := execution
  exact ⟨time,finish,bound,⟨run,halt⟩,store ▸ answer⟩

def machine : Machine.Program := Compiler.compile verifier.program
def machineCoefficient := 20*(verifierCoefficient+133)^2

theorem machine_computes : Complexity.ComputesCleanIn machine
    (fun input=>[Counting.NetworkCertificate.predicate input])
    (Complexity.polynomial machineCoefficient 56) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 27 verifier_computes

/-- The component's Boolean output is the all-agent certificate relation
on the network adapter's final vista list. MachineNetworkVistaRaw supplies
the physical construction of that list and its polynomial cost. -/
theorem machine_network_input (input : Simulation.Input) (certificates : List Encoding.TwoOrderData) :
    ∃ time output,
      time≤Complexity.polynomial machineCoefficient 56
        (Counting.NetworkCertificate.codec.encode
          (Encoding.inputLeaderCount input,(Encoding.inputVistas input).toList,certificates)).length ∧
      Machine.HaltsAt machine (Counting.NetworkCertificate.codec.encode
        (Encoding.inputLeaderCount input,(Encoding.inputVistas input).toList,certificates)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ([Encoding.verifyNetworkWitness input certificates].map Machine.bitSymbol) := by
  obtain ⟨time,output,bound,halt,result⟩ := machine_computes
    (Counting.NetworkCertificate.codec.encode
      (Encoding.inputLeaderCount input,(Encoding.inputVistas input).toList,certificates))
  simp only [Counting.NetworkCertificate.predicate_encoded,Counting.NetworkCertificate.check_inputVistas] at result
  exact ⟨time,output,bound,halt,result⟩

/-- Import-order DAGs use the same physical checker. The certificate
relation depends on their denoted histories, not canonical node numbering. -/
theorem machine_raw_network_input (input : Simulation.Input) (certificates : List Encoding.TwoOrderData) :
    ∃ time output,
      time ≤ Complexity.polynomial machineCoefficient 56
        (Counting.NetworkCertificate.codec.encode
          (Encoding.inputLeaderCount input,(Encoding.rawInputVistas input).toList,certificates)).length ∧
      Machine.HaltsAt machine (Counting.NetworkCertificate.codec.encode
        (Encoding.inputLeaderCount input,(Encoding.rawInputVistas input).toList,certificates)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ([Counting.NetworkCertificate.verifyRawNetworkWitness input certificates].map Machine.bitSymbol) := by
  obtain ⟨time,output,bound,halt,result⟩ := machine_computes
    (Counting.NetworkCertificate.codec.encode
      (Encoding.inputLeaderCount input,(Encoding.rawInputVistas input).toList,certificates))
  simp only [Counting.NetworkCertificate.predicate_encoded] at result
  exact ⟨time,output,bound,halt,result⟩

end Counting.StackMachine.NetworkCertificate
