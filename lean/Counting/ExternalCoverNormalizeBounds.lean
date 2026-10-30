import Counting.ExternalCoverNormalizePrefix

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine MatchingMachine
set_option backward.isDefEq.respectTransparency false

theorem raw_stream_length (raw : MatchingVerification.Raw) :
    (Encoding.sequence MatchingVerification.clauseCodec raw.2).length ≤
      (MatchingVerification.rawCodec.encode raw).length := by
  simp only [MatchingVerification.rawCodec,Encoding.product,Encoding.list,List.length_append]
  omega

theorem raw_universe_length (raw : MatchingVerification.Raw) :
    raw.1.length ≤ (MatchingVerification.rawCodec.encode raw).length := by
  simp only [MatchingVerification.rawCodec,Encoding.product,Encoding.list,List.length_append,sequence_boolean]
  omega

theorem raw_rows_length (raw : MatchingVerification.Raw) :
    raw.2.length ≤ (MatchingVerification.rawCodec.encode raw).length := by
  have positive (row : MatchingVerification.RawClause) : 0<(MatchingVerification.clauseCodec.encode row).length := by
    rw [MatchingVerification.clause_encode,Encoding.list_length]
    omega
  exact (EncodingPrograms.VerifiedParser.sequence_count_le positive raw.2).trans (raw_stream_length raw)

/-- Cost is polynomial in the actual binary source word. In particular the
explicit universe and the number of listed triples are both paid for. -/
theorem normalizePrefix_polynomial (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64)→List Bool) (raw : MatchingVerification.Raw)
    (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=MatchingVerification.rawCodec.encode raw)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈normalizePrefixScratch,store (w i)=[]) :
    ∃ time ≤ 50000*((store (w 0)).length+1)^3,
      Executes (normalizePrefix extra w) store time (prefixResult w store raw) := by
  obtain ⟨time,bound,execution⟩ := normalizePrefix_executes extra w store raw accepted tail source status empty
  have stream := raw_stream_length raw
  have markers := raw_universe_length raw
  have rows := raw_rows_length raw
  rw [←source] at stream markers rows
  let L := (store (w 0)).length+1
  have positive : 1 ≤ L := by dsimp [L];omega
  have prepBase : (store (w 0)).length+raw.1.length+1 ≤ 2*L := by dsimp [L];omega
  have loopBase : 2*(Encoding.sequence MatchingVerification.clauseCodec raw.2).length+1 ≤ 2*L := by dsimp [L];omega
  have countBound : raw.2.length ≤ L := by dsimp [L];omega
  have streamBound : (Encoding.sequence MatchingVerification.clauseCodec raw.2).length ≤ L := by dsimp [L];omega
  have prepLimit : 4000*((store (w 0)).length+raw.1.length+1)^3 ≤ 32000*L^3 := by
    calc _ ≤ 4000*(2*L)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left prepBase 3)
         _ = _ := by ring
  have loopLimit : raw.2.length*(2000*(2*(Encoding.sequence MatchingVerification.clauseCodec raw.2).length+1)^2+2) ≤
      8000*L^3+2*L := by
    calc _ ≤ L*(2000*(2*L)^2+2) := by gcongr
         _ = _ := by ring
  have linear : L ≤ L^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ L^3 := Nat.one_le_pow _ _ positive
  refine ⟨time,?_,execution⟩
  change time ≤ 50000*L^3
  omega

end Counting.External.CoverNormalization
