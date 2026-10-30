import Counting.ExternalCoverNormalizeGenerator

namespace Counting.External.CoverNormalization
open MatchingMachine

theorem consecutiveRow_length (u : Nat) :
    (MatchingVerification.clauseCodec.encode (consecutiveRow u)).length ≤ 6*u+20 := by
  have a : u.size ≤ u := Nat.size_le.mpr Nat.lt_two_pow_self
  have b : (u+1).size ≤ u+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have c : (u+2).size ≤ u+2 := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [MatchingVerification.clause_encode,Encoding.list_length]
  simp only [consecutiveRow,MatchingVerification.clauseToRaw,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,MatchingVerification.literalCodec,Encoding.natural_length]
  simp only [show (0+1+1+1 : Nat).size=2 by decide]
  omega

theorem paddingRows_stream_length (u : Nat) :
    (Encoding.sequence MatchingVerification.clauseCodec (paddingRows u)).length ≤ 12*u+58 := by
  have first := consecutiveRow_length (u+3)
  have second := consecutiveRow_length u
  simp only [paddingRows,Encoding.sequence,List.length_append,List.length_nil]
  omega

theorem normalized_stream_length (raw : MatchingVerification.Raw) :
    (Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2).length ≤
      100*((MatchingVerification.rawCodec.encode raw).length+1) := by
  have pad := paddingRows_stream_length raw.1.length
  have rest := freshRows_sequence_length [] raw.2
  have markers := raw_universe_length raw
  have stream := raw_stream_length raw
  simp only [normalizedRaw,rowSequence_append,List.length_append]
  omega

/-- Cubic cost in the actual serialized source, including explicit output
markers. Large binary coordinates do not become unary loop counters. -/
theorem generatorCost_polynomial (raw : MatchingVerification.Raw) :
    generatorCost (MatchingVerification.rawCodec.encode raw).length raw ≤
      100000*((MatchingVerification.rawCodec.encode raw).length+1)^3 := by
  let L := (MatchingVerification.rawCodec.encode raw).length+1
  have positive : 1 ≤ L := by dsimp [L];omega
  have universeBound : raw.1.length ≤ L := (raw_universe_length raw).trans (by dsimp [L];omega)
  have countBound : (freshRows [] raw.2).length ≤ L :=
    (freshRows_length [] raw.2).trans ((raw_rows_length raw).trans (by dsimp [L];omega))
  have streamBound : (Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2).length ≤ 100*L :=
    normalized_stream_length raw
  have square6 : (raw.1.length+6)^2 ≤ 49*L^2 := by
    calc _ ≤ (7*L)^2 := Nat.pow_le_pow_left (by omega) 2
         _ = _ := by ring
  have square7 : (raw.1.length+6+1)^2 ≤ 64*L^2 := by
    calc _ ≤ (8*L)^2 := Nat.pow_le_pow_left (by omega) 2
         _ = _ := by ring
  have square3 : ((freshRows [] raw.2).length+2+1)^2 ≤ 16*L^2 := by
    calc _ ≤ (4*L)^2 := Nat.pow_le_pow_left (by omega) 2
         _ = _ := by ring
  have square : L^2 ≤ L^3 := Nat.pow_le_pow_right positive (by decide)
  have linear : L ≤ L^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ L^3 := Nat.one_le_pow _ _ positive
  change generatorCost _ _ ≤ 100000*L^3
  dsimp only [generatorCost,finishCost,matchingFinalizeCost]
  change 250*(raw.1.length+6)^2+50000*L^3+
    (5*raw.1.length+5*(freshRows [] raw.2).length+30+
    (2*(Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2).length+
    20*((freshRows [] raw.2).length+2+1)^2+28*(raw.1.length+6+1)^2+6))+2 ≤ _
  omega

end Counting.External.CoverNormalization
