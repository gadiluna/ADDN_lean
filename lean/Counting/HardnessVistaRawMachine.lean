import Counting.MachineNetworkVistaRaw
import Counting.MachineVistaFirst
import Counting.HardnessVistaRawTarget
import Counting.HardnessNetworkMachineReduction

namespace Counting.HardnessVistaRaw
open Machine Complexity
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000
set_option exponentiation.threshold 1024

private theorem selectorCost_bound (c d N a b : Nat) (positive : 1≤N)
    (first : a≤c*N^746) (second : b≤d*N^48) :
    a+1+b ≤ (c+d+1)*N^746 := by
  have power : N^48≤N^746 := Nat.pow_le_pow_right positive (by decide)
  have last := second.trans (Nat.mul_le_mul_left d power)
  have one : 1≤N^746 := one_le_pow₀ positive
  rw [Nat.add_mul,Nat.add_mul]
  omega

def firstSelectorCoefficient : Nat := 20*(12000+23)^2*204^8
def extractorProgram : Machine.Program := Machine.compose networkVistaRawProgram vistaFirstProgram
def extractorCoefficient : Nat := networkVistaRawCoefficient+firstSelectorCoefficient+1

/-- A real reconstruction machine followed by a real first-observer
selector. The premise is supplied unconditionally by source normalization. -/
theorem extractor_clean (input : Simulation.Input) (valid : Encoding.networkValid input=true) :
    ∃ time output,
      time ≤ polynomial extractorCoefficient 746 (Encoding.networkInput.encode input).length ∧
      HaltsAt extractorProgram (Encoding.networkInput.encode input) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((firstWord input).map bitSymbol) := by
  obtain ⟨t0,o0,b0,r0,e0⟩ := networkVistaRaw_clean input valid
  obtain ⟨t1,o1,b1,r1,e1⟩ := vistaFirst_raw_input_polynomial input
    ((Encoding.networkValid_iff input).mp valid).1
  obtain ⟨output,halted,tape⟩ := compose_halts r0 e0 r1
  refine ⟨t0+1+t1,output,?_,halted,tape.trans e1⟩
  exact selectorCost_bound networkVistaRawCoefficient firstSelectorCoefficient _ _ _ (by omega) b0 b1

def normalizedVistaProgram : Machine.Program :=
  Machine.compose HardnessNetworkMachine.normalizedNetworkMachine extractorProgram

def normalizedVistaCoefficient : Nat := compositionCoefficient
  HardnessNetworkMachine.normalizedNetworkCoefficient extractorCoefficient 746

def normalizedVistaExponent : Nat := compositionExponent
  HardnessNetworkMachine.normalizedNetworkExponent 746

/-- Every bitword passes through the proved total X3C normalizer, the
physical network constructor, offline distributed execution, and observer
extraction. No unproved runtime or transducer assumption remains. -/
theorem normalizedVista_computesCleanIn :
    ComputesCleanIn normalizedVistaProgram normalizedVista
      (polynomial normalizedVistaCoefficient normalizedVistaExponent) := by
  intro word
  obtain ⟨t0,o0,b0,r0,e0⟩ := HardnessNetworkMachine.normalizedNetworkMachine_computesCleanIn word
  obtain ⟨input,encoded,valid,_,_,result⟩ := normalizedNetwork_target word
  obtain ⟨t1,o1,b1,r1,e1⟩ := extractor_clean input valid
  rw [encoded] at b1 r1
  rw [←result] at e1
  obtain ⟨output,halted,tape⟩ := compose_halts r0 e0 r1
  refine ⟨t0+1+t1,output,?_,halted,tape.trans e1⟩
  have length := HardnessNetworkMachine.normalizedNetworkMachine_computesCleanIn.output_length word
  have total := polynomial_composition_bound word.length (HardnessNetworkMachine.normalizedNetwork word).length
    HardnessNetworkMachine.normalizedNetworkCoefficient HardnessNetworkMachine.normalizedNetworkExponent
    extractorCoefficient 746 length
  exact (Nat.add_le_add_right (Nat.add_le_add_right b0 1) t1).trans
    ((Nat.add_le_add_left b1 _).trans total)

end Counting.HardnessVistaRaw
