import Counting.StackNetworkComplementGuarded

namespace Counting.StackMachine.NetworkComplement
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 2200000

def finish : Routine 158 := ofProgram (ListPrograms.copyProgram 157 (context 7) 1 0)

theorem finish_executes (data : Fin 30→List Bool) (bit : Bool) (value : data 7=[bit]) :
    ∃result, Executes finish (file data) 7 result ∧ result 1=[bit] := by
  have run := copy_executes 157 (context 7) 1 0
    (context_ne_local 7 1 (by decide)) (context_ne_local 7 0 (by decide)) (by decide)
    (file data) (by simp)
  rw [file_context,value,show file data 1=[] by simp,List.append_nil] at run
  exact ⟨Function.update (file data) 1 [bit],run,by simp⟩

def predicate (input : List Bool) : Bool := (Encoding.unframe input).isSome &&
  Counting.NetworkCertificate.binaryRawNetworkComplementVerifier (unframePayload input) (unframeSuffix input)

def verifier : Routine 158 := sequence prepare (sequence guarded finish)
def verifierCoefficient : Nat := 2^373*guardedCoefficient+20

/-- Every input word halts. Malformed framing rejects, an invalid encoded
network accepts the complement, and valid networks use all reconstructed
agent views with the actual leader count and the supplied certificate. -/
theorem verifier_executes (input : List Bool) :
    ∃time≤Complexity.polynomial verifierCoefficient 373 input.length,
      ∃result, Executes verifier (inputStore 158 input) time result ∧ result 1=[predicate input] := by
  obtain ⟨t0,b0,r0⟩ := prepare_executes input
  let ready := initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome
  obtain ⟨t1,b1,checked,r1,output⟩ := guarded_executes ready (Encoding.unframe input).isSome
    (by simp [ready,initialData]) (by
      intro r member
      fin_cases r <;> simp_all [ready,initialData])
  have inputAt : ready 0=unframePayload input := by simp [ready,initialData]
  have witnessAt : ready 1=unframeSuffix input := by simp [ready,initialData]
  rw [inputAt,witnessAt] at b1 output
  obtain ⟨result,r2,answer⟩ := finish_executes checked (predicate input) output
  have inputBound := unframe_payload_length input
  have witnessBound := unframe_suffix_length input
  have power : ((unframePayload input).length+(unframeSuffix input).length+1)^373≤
      2^373*(input.length+1)^373 := by
    calc
      _≤(2*(input.length+1))^373 := Nat.pow_le_pow_left (by omega) 373
      _=_ := Nat.mul_pow _ _ _
  have checkedBound : t1≤(2^373*guardedCoefficient)*(input.length+1)^373 := by
    change t1≤guardedCoefficient*((unframePayload input).length+(unframeSuffix input).length+1)^373 at b1
    exact b1.trans (by simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left guardedCoefficient power)
  have linear : input.length+1≤(input.length+1)^373 := Nat.le_self_pow (by decide) _
  have one : 1≤(input.length+1)^373 := Nat.one_le_pow' _ _
  refine ⟨t0+1+(t1+1+7),?_,result,r0.sequence (r1.sequence r2),answer⟩
  change _≤(2^373*guardedCoefficient+20)*(input.length+1)^373
  rw [Nat.add_mul]
  omega

theorem predicate_pairWords (input witness : List Bool) :
    predicate (Encoding.pairWords input witness)=
      Counting.NetworkCertificate.binaryRawNetworkComplementVerifier input witness := by
  simp [predicate,Encoding.pairWords,unframePayload,unframeSuffix,Encoding.unframe_frame]

end Counting.StackMachine.NetworkComplement
