import Counting.StackRealizabilityTotal
import Counting.StackCompilerComplete

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem encodedVerifier_encode (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    encodedVerifier (Encoding.verifierInput.encode (vista,values,ell,order))=
      RealizabilityVerifier.verify vista values.toArray ell order := by
  have parsed := (Encoding.Codec.decodeExact_iff Encoding.verifierInput _ (vista,values,ell,order)).mpr rfl
  simp only [encodedVerifier,parsed]

theorem verifier_computes : ComputesIn totalVerifier.program
    (fun input=>[encodedVerifier input]) (Complexity.polynomial verifierCoefficient 25) := by
  intro input
  obtain ⟨time,bound,result,execution,answer⟩ := totalVerifier_executes input
  obtain ⟨finish,run,halt,store⟩ := execution
  exact ⟨time,finish,bound,⟨run,halt⟩,store ▸ answer⟩

/-- A finite-state, finite-alphabet Turing machine for the complete compact
certificate verifier, including malformed-input rejection and clean output. -/
def certificateMachine : Machine.Program := Compiler.compile totalVerifier.program

def certificateMachineCoefficient : Nat := 20*(verifierCoefficient+103)^2

/-- Every step is a physical Turing transition. The exponent is deliberately
coarse; no unit-cost arithmetic, uncharged graph oracle or unary population
expansion is used by this certificate machine. -/
theorem certificateMachine_computes : Complexity.ComputesCleanIn certificateMachine
    (fun input=>[encodedVerifier input]) (Complexity.polynomial certificateMachineCoefficient 52) := by
  exact Compiler.computesCleanIn_polynomial verifierCoefficient 25 verifier_computes

end Counting.StackMachine.RealizabilityCheck
