import Counting.ExternalMatchingGenerator

namespace Counting.External.MatchingMachine

/-- This envelope uses the bit length of the actual input and includes
all counting, parsing, emission, reversal and final-header operations. -/
theorem matchingGeneratorCost_polynomial (length n m stream : Nat)
    (nBound : n≤length) (mBound : m≤length)
    (streamBound : stream≤MatchingDimensions.edges n m*(6*MatchingDimensions.order n m+8)) :
    matchingGeneratorCost length n m stream≤1000000000000*(length+1)^9 := by
  let s := length*(3*length+1)
  let q := 2*s
  let e := q+3*length+s*q
  have slotsBound : MatchingDimensions.slots n m≤ s := by
    dsimp only [MatchingDimensions.slots,s]
    gcongr
  have orderBound : MatchingDimensions.order n m≤ q := Nat.mul_le_mul_left 2 slotsBound
  have garbageBound : MatchingDimensions.garbage n m≤ s := (Nat.sub_le _ _).trans slotsBound
  have edgeBound : MatchingDimensions.edges n m≤ e := by
    dsimp only [MatchingDimensions.edges,e]
    gcongr
  have streamLimit : stream≤ e*(6*q+8) := by
    apply streamBound.trans
    gcongr
  have dimensionLimit : MatchingDimensions.cost n m≤ 20*s+15*s+11*(s*q)+5*q+9*length+37*length+67 := by
    dsimp only [MatchingDimensions.cost]
    gcongr
  have variableLimit : variablePartCost n m (MatchingDimensions.slots n m)≤ variablePartCost length length s := by
    dsimp only [variablePartCost]
    gcongr
  have clauseLimit : clausePartCost length n m (3*m+1) (MatchingDimensions.slots n m)≤ clausePartCost length length length (3*length+1) s := by
    dsimp only [clausePartCost]
    gcongr
  have completionLimit : completionPartCost (MatchingDimensions.slots n m+m) (MatchingDimensions.order n m)
      (MatchingDimensions.garbage n m)≤ completionPartCost (s+length) q s := by
    dsimp only [completionPartCost]
    gcongr
  have finalizeLimit : matchingFinalizeCost (MatchingDimensions.order n m) (MatchingDimensions.edges n m) stream≤
      matchingFinalizeCost q e (e*(6*q+8)) := by
    dsimp only [matchingFinalizeCost]
    gcongr
  calc
    matchingGeneratorCost length n m stream≤ 20*s+15*s+11*(s*q)+5*q+9*length+37*length+67+1+
      (4000*(length+length+1)^3+1+(variablePartCost length length s+1+
        (clausePartCost length length length (3*length+1) s+1+
          (completionPartCost (s+length) q s+1+matchingFinalizeCost q e (e*(6*q+8)))))) := by
      dsimp only [matchingGeneratorCost]
      gcongr
    _ ≤1000000000000*(length+1)^9 := by
      dsimp only [variablePartCost,clausePartCost,completionPartCost,matchingFinalizeCost,s,q,e]
      ring_nf
      omega

end Counting.External.MatchingMachine
