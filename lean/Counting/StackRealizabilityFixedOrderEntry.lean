import Counting.StackRealizabilityFixedOrderGuarded
import Counting.StackRealizabilityVistaEntry

namespace Counting.StackMachine.FixedOrderRecognition
open Routine RealizabilityCall EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def predicate (input : List Bool) : Bool := (Encoding.unframe input).isSome &&
  Encoding.binaryFixedOrderVerifier (unframePayload input) (unframeSuffix input)

def verifier : Routine 128 := sequence VistaComplement.prepare (sequence guarded VistaComplement.finish)
def verifierCoefficient : Nat := 2^25*guardedCoefficient+20

theorem verifier_executes (input : List Bool) :
    ∃time≤Complexity.polynomial verifierCoefficient 25 input.length,
      ∃result, Executes verifier (inputStore 128 input) time result ∧ result 1=[predicate input] := by
  obtain ⟨t0,b0,r0⟩ := VistaComplement.prepare_executes input
  let ready := VistaComplement.initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome
  obtain ⟨t1,b1,checked,r1,output⟩ := guarded_executes ready (Encoding.unframe input).isSome []
    (by simp [ready,VistaComplement.initialData]) (by
      intro i hi
      rcases hi with h|h|h|h|h <;> subst i <;> simp [ready,VistaComplement.initialData])
  have inputAt : ready 8=unframePayload input := by simp [ready,VistaComplement.initialData]
  have witnessAt : ready 9=unframeSuffix input := by simp [ready,VistaComplement.initialData]
  rw [inputAt,witnessAt] at b1 output
  obtain ⟨result,r2,resultAt⟩ := VistaComplement.finish_executes checked (predicate input) output
  refine ⟨t0+1+(t1+1+3),?_,result,r0.sequence (r1.sequence r2),resultAt⟩
  have inBound := unframe_payload_length input
  have witnessBound := unframe_suffix_length input
  have power : ((unframePayload input).length+(unframeSuffix input).length+1)^25≤2^25*(input.length+1)^25 := by
    calc
      _≤(2*(input.length+1))^25 := Nat.pow_le_pow_left (by omega) 25
      _=_ := Nat.mul_pow _ _ _
  have checkBound := b1.trans (Nat.mul_le_mul_left guardedCoefficient power)
  have linear : input.length+1≤(input.length+1)^25 := Nat.le_self_pow (by decide) _
  change _≤(2^25*guardedCoefficient+20)*(input.length+1)^25
  simp only [Nat.add_mul,Nat.mul_assoc]
  change t1≤guardedCoefficient*(2^25*(input.length+1)^25) at checkBound
  have rearrange : guardedCoefficient*(2^25*(input.length+1)^25)=2^25*(guardedCoefficient*(input.length+1)^25) := by ring
  rw [rearrange] at checkBound
  omega

theorem predicate_pairWords (input witness : List Bool) :
    predicate (Encoding.pairWords input witness)=Encoding.binaryFixedOrderVerifier input witness := by
  simp [predicate,Encoding.pairWords,unframePayload,unframeSuffix,Encoding.unframe_frame]

end Counting.StackMachine.FixedOrderRecognition
