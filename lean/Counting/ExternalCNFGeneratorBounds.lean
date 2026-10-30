import Counting.ExternalCNFGenerator

namespace Counting.External.CNFMachine

/-- A uniform bound in the actual input length, after discharging variable,
clause, width and emitted-stream bounds from the canonical input codec. -/
theorem formulaGeneratorCost_polynomial (length n m width stream : Nat)
    (nBound : n ≤ length) (mBound : m ≤ length) (widthBound : width ≤ length)
    (streamBound : stream ≤ m*(3*width+2)*(6*(n+m*(width+1))+11)) :
    formulaGeneratorCost length n m width stream ≤ 1000000000*(length+1)^7 := by
  have streamLimit : stream ≤ length*(3*length+2)*(6*(length+length*(length+1))+11) := by
    apply streamBound.trans
    gcongr
  calc
    formulaGeneratorCost length n m width stream ≤
        formulaGeneratorCost length length length length
          (length*(3*length+2)*(6*(length+length*(length+1))+11)) := by
      dsimp only [formulaGeneratorCost,formulaFinalizeCost,formulaCodeLimit]
      gcongr
    _ ≤ 1000000000*(length+1)^7 := by
      dsimp only [formulaGeneratorCost,formulaFinalizeCost,formulaCodeLimit]
      ring_nf
      omega

end Counting.External.CNFMachine
