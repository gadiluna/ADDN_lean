import Counting.StackRealizabilityDepthUnary

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def depthCounter : Routine 98 := sequence depthPrepare
  (sequence depthRead (sequence depthFrame depthUnary))

/-- The complete preparation of the loop counter, including source and
index copies, node lookup, metadata decoding, canonical framing, bounded
conversion and cleanup. Its cost is independent of numeric population. -/
theorem depthCounter_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 100000*(((Encoding.list Encoding.node).encode vista.nodes.toList).length+vista.nodes.size+1)^4,
      Executes depthCounter (inputCountStore vista values ell order (accepted::tail)) time
        (roundsReadyStore vista values ell order (accepted::tail)) := by
  obtain ⟨t0,b0,r0⟩ := depthPrepare_executes vista values ell order (accepted::tail)
  obtain ⟨t1,b1,r1⟩ := depthRead_executes vista values ell order valid accepted tail
  obtain ⟨t2,b2,r2⟩ := depthFrame_executes vista values ell order valid (accepted::tail)
  obtain ⟨t3,b3,r3⟩ := depthUnary_executes vista values ell order valid accepted tail
  let word := (Encoding.list Encoding.node).encode vista.nodes.toList
  let S := word.length+vista.nodes.size+1
  change t0 ≤ 20*S at b0
  change t2 ≤ 30*S at b2
  have positive : 1 ≤ S := by dsimp only [S];omega
  have sequenceSmall : (Encoding.sequence Encoding.node vista.nodes.toList).length ≤ word.length := by
    change _ ≤ (Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList).length
    rw [List.length_append];omega
  have readLimit : t1 ≤ 7000*S^4 := b1.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 4))
  have depthBound := RealizabilityVerifier.valid_depth_lt_size vista valid
  have depthSize : (vista.node vista.bottom).level.size ≤ (vista.node vista.bottom).level :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have unaryBase : vista.nodes.size+(Encoding.natural.encode (vista.node vista.bottom).level).length+1 ≤ 3*S := by
    rw [Encoding.natural_length]
    dsimp only [S];omega
  have unaryLimit : t3 ≤ 2700*S^3 := by
    have scale (n:Nat) : 100*(3*n)^3=2700*n^3 := by ring
    exact (b3.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left unaryBase 3))).trans_eq (scale S)
  have cube : S^3 ≤ S^4 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4 := Nat.one_le_pow _ _ positive
  exact ⟨_,by change t0+1+(t1+1+(t2+1+t3)) ≤ 100000*S^4;omega,
    r0.sequence (r1.sequence (r2.sequence r3))⟩

end Counting.StackMachine.RealizabilityCheck
