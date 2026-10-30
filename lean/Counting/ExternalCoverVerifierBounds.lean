import Counting.ExternalCoverElementAudit

namespace Counting.External.CoverVerification

theorem elementAuditCost_polynomial (stream count index length : Nat)
    (streamBound : stream ≤ length) (countBound : count ≤ length) (indexBound : index ≤ length) :
    elementAuditCost stream count index ≤ 100000*(length+1)^4 := by
  have sizeBound : index.size ≤ length := (Nat.size_le.mpr Nat.lt_two_pow_self).trans indexBound
  have large : elementAuditCost stream count index ≤
      5*(length+length+length)+9+20*(length+1)^2+1+
        (length*(2100*(length+(2*length+1)+1)^3+2)+1+1+
          (length+15+1+((2*length+1)+1+1+1))) := by
    simp only [elementAuditCost,prepareElementCost,Encoding.natural_length]
    gcongr
  apply large.trans
  ring_nf
  omega

end Counting.External.CoverVerification
