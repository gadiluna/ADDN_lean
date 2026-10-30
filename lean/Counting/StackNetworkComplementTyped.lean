import Counting.StackNetworkComplementEntry
import Counting.StackNetworkComplementCalls
import Counting.NetworkCertificatePrefix
import Counting.NetworkVistaRunComplete

namespace Counting.StackMachine.NetworkComplement
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 2200000

def reconstruct : Routine 158 := call NetworkVista.Run.complete (by decide) 0 5

def typed : Routine 158 := sequence countLeaders
  (sequence reconstruct (sequence assemble checkCertificates))

def typedCoefficient : Nat := NetworkVista.Run.completeCoefficient+checkCoefficient*208^27+10000

def typedData (data : Fin 30→List Bool) (input : Simulation.Input) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update data
    4 (Encoding.natural.encode (Encoding.inputLeaderCount input)))
    5 ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)))
    6 (Counting.NetworkCertificate.inputWord (Encoding.inputLeaderCount input)
      (Encoding.rawInputVistas input) (data 1)))
    7 [Counting.NetworkCertificate.binaryRawNetworkComplementVerifier (data 0) (data 1)]

/-- On a validated network, physically reconstruct every final DAG,
count the initial leaders, and run the total compact-certificate checker. -/
theorem typed_executes (data : Fin 30→List Bool) (input : Simulation.Input)
    (valid : Encoding.networkValid input=true) (source : data 0=Encoding.networkInput.encode input)
    (empty : ∀r:Fin 30,r∈([4,5,6,7]:List (Fin 30)) → data r=[]) :
    ∃time≤Complexity.polynomial typedCoefficient 373 ((data 0).length+(data 1).length),
      Executes typed (file data) time (file (typedData data input)) := by
  obtain ⟨t0,b0,r0⟩ := countLeaders_executes data input source (empty 4 (by simp))
  let d1 := Function.update data 4 (Encoding.natural.encode (Encoding.inputLeaderCount input))
  obtain ⟨t1,b1,r1⟩ := NetworkVista.Run.complete_executes input valid
  have ready : d1 0=Encoding.networkInput.encode input := by simp [d1,source]
  rw [← ready] at r1 b1
  have r1' := call_executes NetworkVista.Run.complete (by decide) d1 0 5
    (by simp [d1,empty 5 (by simp)]) _ t1 r1
  let views := (Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input)
  let d2 := Function.update d1 5 views
  have r2 := assemble_executes d2 (by simp [d2,d1,empty 6 (by simp)])
  let word := Counting.NetworkCertificate.inputWord (Encoding.inputLeaderCount input)
    (Encoding.rawInputVistas input) (data 1)
  have assembled : d2 4++d2 5++d2 1=word := by simp [d2,d1,word,Counting.NetworkCertificate.inputWord,views]
  rw [assembled] at r2
  let d3 := Function.update d2 6 word
  obtain ⟨t3,b3,r3⟩ := checkCertificates_executes d3 (by simp [d3,d2,d1,empty 7 (by simp)])
  have checked : Counting.NetworkCertificate.predicate (d3 6)=
      Counting.NetworkCertificate.binaryRawNetworkComplementVerifier (data 0) (data 1) := by
    change Counting.NetworkCertificate.predicate word=_
    rw [source]
    exact Counting.NetworkCertificate.predicate_raw_inputWord input (data 1) valid
  rw [checked] at r3
  let N := (data 0).length+(data 1).length+1
  have positive : 1≤N := by dsimp [N];omega
  have inputBound : (data 0).length+1≤N := by dsimp [N];omega
  have witnessBound : (data 1).length≤N := by dsimp [N];omega
  have p3 : ((data 0).length+1)^3≤N^373 :=
    (Nat.pow_le_pow_left inputBound 3).trans (Nat.pow_le_pow_right positive (by decide))
  have p373 : ((data 0).length+1)^373≤N^373 := Nat.pow_le_pow_left inputBound 373
  have p6 : N^6≤N^373 := Nat.pow_le_pow_right positive (by decide)
  have linear : N≤N^6 := Nat.le_self_pow (by decide) _
  have one6 : 1≤N^6 := Nat.one_le_pow _ _ positive
  have one : 1≤N^373 := Nat.one_le_pow _ _ positive
  have vbound : views.length≤203*N^6 := by
    have old := NetworkVista.Run.viewArray_length_bound input input.rounds.size (by omega)
    change views.length≤203*((Encoding.networkInput.encode input).length+1)^6 at old
    rw [← source] at old
    exact old.trans (Nat.mul_le_mul_left 203 (Nat.pow_le_pow_left inputBound 6))
  have leaders : Encoding.inputLeaderCount input≤(data 0).length := by
    rw [source,Encoding.inputLeaderCount_eq_count]
    exact (List.count_le_length (a:=true) (l:=input.leaders.toList)).trans
      (by simpa only [Array.length_toList] using Encoding.network_agents_le_length input)
  have leaderSize : (Encoding.inputLeaderCount input).size≤Encoding.inputLeaderCount input :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have ellbound : (Encoding.natural.encode (Encoding.inputLeaderCount input)).length≤3*N^6 := by
    rw [Encoding.natural_length]
    omega
  have wordBound : word.length+1≤208*N^6 := by
    change (Encoding.natural.encode (Encoding.inputLeaderCount input)++views++data 1).length+1≤208*N^6
    simp only [List.length_append]
    omega
  have power27 := Nat.pow_le_pow_left wordBound 27
  have power162 : (208*N^6)^27=208^27*N^162 := by rw [Nat.mul_pow,← Nat.pow_mul]
  rw [power162] at power27
  have p162 : N^162≤N^373 := Nat.pow_le_pow_right positive (by decide)
  have checkerBound : t3≤(checkCoefficient*208^27)*N^373 := by
    change t3≤checkCoefficient*(word.length+1)^27 at b3
    exact b3.trans ((Nat.mul_le_mul_left checkCoefficient power27).trans (by
      simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left (checkCoefficient*208^27) p162))
  have firstBound := b0.trans (Nat.mul_le_mul_left 3100 p3)
  have runBound : t1≤NetworkVista.Run.completeCoefficient*N^373 := by
    change t1≤NetworkVista.Run.completeCoefficient*((data 0).length+1)^373 at b1
    exact b1.trans (Nat.mul_le_mul_left _ p373)
  have codeBounds : (d2 1).length+(d2 5).length+(d2 4).length≤207*N^6 := by
    simp only [d2,d1,Function.update_of_ne (by decide : (1:Fin 30)≠5),
      Function.update_of_ne (by decide : (1:Fin 30)≠4),Function.update_self,
      Function.update_of_ne (by decide : (4:Fin 30)≠5)]
    omega
  have copiedInput : (d1 0).length=(data 0).length := by simp [d1]
  have composed := r0.sequence (r1'.sequence (r2.sequence r3))
  change Executes typed (file data)
    (t0+1+(5*(d1 0).length+6*views.length+t1+8+1+
      (5*((d2 1).length+(d2 5).length+(d2 4).length)+8+1+t3)))
    (file (typedData data input)) at composed
  refine ⟨_,?_,composed⟩
  rw [copiedInput]
  change _≤(NetworkVista.Run.completeCoefficient+checkCoefficient*208^27+10000)*N^373
  rw [Nat.add_mul,Nat.add_mul]
  have viewScale := Nat.mul_le_mul_left 203 p6
  have codeScale := Nat.mul_le_mul_left 207 p6
  have inputScale : (data 0).length≤N^373 := by omega
  omega

end Counting.StackMachine.NetworkComplement
