import Counting.StackAnchorCoefficient

namespace Counting.StackMachine.AnchorCoefficient
open Routine EncodingPrograms

theorem difference_word_length (first second : Nat) :
    (Encoding.rational.encode ((first:Rat)-second)).length ≤ 1000*(first.size+second.size+1) := by
  let input := AnchorDifference.arguments first.bits second.bits
  have outputBound := computed_length_le Signed.signedAdditionRoutine _ _ Signed.signedAddition_computes input
  have inputLength : input.length=2*first.size+2*second.size+4 := by
    simp [input,AnchorDifference.arguments,Encoding.frame_length,Encoding.bits_length]
    omega
  have resultWord : Signed.signedAdditionFunction input++Encoding.natural.encode 1=
      Encoding.rational.encode ((first:Rat)-second) := by
    rw [AnchorDifference.signed_arguments,←AnchorDifference.rational_int_encode]
    simp
  simp only [Complexity.polynomial,pow_one] at outputBound
  rw [←resultWord,List.length_append]
  have one : (Encoding.natural.encode 1).length=3 := rfl
  rw [one]
  omega

theorem coefficient_word_length (node : Executable.Node) (query : Nat) :
    (Encoding.rational.encode (coefficient node query)).length ≤
      2000*((Encoding.node.encode node).length+1) := by
  have bounded := difference_word_length (Executable.countFrom node query) (chargedDegree node query)
  have red := Encoding.redBits_le_node node query
  have degree := Encoding.degreeBits_le_node node
  have selected : (chargedDegree node query).size ≤ node.degree.size := by
    unfold chargedDegree;split <;> simp
  change (Encoding.rational.encode (coefficient node query)).length ≤ _ at bounded
  rw [Encoding.node_length]
  omega

end Counting.StackMachine.AnchorCoefficient
