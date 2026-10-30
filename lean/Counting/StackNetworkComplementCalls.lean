import Counting.StackNetworkComplementFile
import Counting.StackNetworkComplementLeaders
import Counting.NetworkRecognitionMachine
import Counting.MachineNetworkCertificate

namespace Counting.StackMachine.NetworkComplement
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 1800000

def validate : Routine 158 := call (isolate NetworkRecognition.totalNetworkCheck) (by decide) 0 3

theorem validate_executes (data : Fin 30→List Bool) (empty : data 3=[]) :
    ∃time≤2000000000000*((data 0).length+1)^7,
      Executes validate (file data) time
        (file (Function.update data 3 [NetworkRecognition.validNetworkWord (data 0)])) := by
  obtain ⟨time,bound,run⟩ := isolate_executes NetworkRecognition.totalNetworkCheck _ _
    NetworkRecognition.totalNetworkCheck_computes (data 0)
  have called := call_executes (isolate NetworkRecognition.totalNetworkCheck) (by decide) data 0 3 empty
    [NetworkRecognition.validNetworkWord (data 0)] time run
  simp only [NetworkRecognition.totalNetworkExponent_eq,NetworkRecognition.totalNetworkCoefficient_eq,
    Complexity.polynomial] at bound
  have linear : (data 0).length+1≤((data 0).length+1)^7 := Nat.le_self_pow (by decide) _
  have one : 1≤((data 0).length+1)^7 := Nat.one_le_pow _ _ (by omega)
  refine ⟨5*(data 0).length+6+time+8,by omega,called⟩

def countLeaders : Routine 158 := call leaderCount (by decide) 0 4

theorem countLeaders_executes (data : Fin 30→List Bool) (input : Simulation.Input)
    (source : data 0=Encoding.networkInput.encode input) (empty : data 4=[]) :
    ∃time≤3100*((data 0).length+1)^3,
      Executes countLeaders (file data) time
        (file (Function.update data 4 (Encoding.natural.encode (Encoding.inputLeaderCount input)))) := by
  obtain ⟨time,bound,run⟩ := leaderCount_executes input
  rw [← source] at run bound
  have called := call_executes leaderCount (by decide) data 0 4 empty _ time run
  have countBound : Encoding.inputLeaderCount input≤(data 0).length := by
    rw [source,Encoding.inputLeaderCount_eq_count]
    exact (List.count_le_length (a:=true) (l:=input.leaders.toList)).trans
      (by simpa only [Array.length_toList] using Encoding.network_agents_le_length input)
  have sizeBound : (Encoding.inputLeaderCount input).size≤Encoding.inputLeaderCount input :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have encoded : (Encoding.natural.encode (Encoding.inputLeaderCount input)).length≤3*((data 0).length+1) := by
    rw [Encoding.natural_length];omega
  have linear : (data 0).length+1≤((data 0).length+1)^3 := Nat.le_self_pow (by decide) _
  have one : 1≤((data 0).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,called⟩

def checkCertificates : Routine 158 := call (isolate StackMachine.NetworkCertificate.verifier) (by decide) 6 7
def checkCoefficient : Nat := 131*(StackMachine.NetworkCertificate.verifierCoefficient+4)+30

theorem checkCertificates_executes (data : Fin 30→List Bool) (empty : data 7=[]) :
    ∃time≤Complexity.polynomial checkCoefficient 27 (data 6).length,
      Executes checkCertificates (file data) time
        (file (Function.update data 7 [Counting.NetworkCertificate.predicate (data 6)])) := by
  obtain ⟨time,bound,run⟩ := isolate_executes StackMachine.NetworkCertificate.verifier _ _
    StackMachine.NetworkCertificate.verifier_computes (data 6)
  have called := call_executes (isolate StackMachine.NetworkCertificate.verifier) (by decide) data 6 7 empty
    [Counting.NetworkCertificate.predicate (data 6)] time run
  have linear : (data 6).length+1≤((data 6).length+1)^27 := Nat.le_self_pow (by decide) _
  have one : 1≤((data 6).length+1)^27 := Nat.one_le_pow _ _ (by omega)
  change time≤131*(StackMachine.NetworkCertificate.verifierCoefficient*((data 6).length+1)^27+(data 6).length+3) at bound
  refine ⟨5*(data 6).length+6+time+8,?_,called⟩
  change _≤(131*(StackMachine.NetworkCertificate.verifierCoefficient+4)+30)*((data 6).length+1)^27
  simp only [Nat.add_mul,Nat.mul_assoc]
  omega

end Counting.StackMachine.NetworkComplement
