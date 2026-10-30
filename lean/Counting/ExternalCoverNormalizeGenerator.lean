import Counting.ExternalCoverNormalizeBounds
import Counting.ExternalCoverNormalizeRaw
import Counting.ExternalCoverNormalizeFinish

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def paddingPositions : Fin 6 ↪ Fin 64 := ⟨![17,36,32,18,19,44],by decide⟩
def paddingWorkspace (w : GeneratorWorkspace extra) : EmitWorkspace (extra+58) := paddingPositions.trans w

def generator (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (emitPadding (extra+58) (paddingWorkspace w))
    (sequence (normalizePrefix extra w) (finish extra w))

def generatorCost (sourceLength : Nat) (raw : MatchingVerification.Raw) :=
  250*(raw.1.length+6)^2+50000*(sourceLength+1)^3+
    finishCost raw.1.length (freshRows [] raw.2).length
      (Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2).length+2

def generatorResult (w : GeneratorWorkspace extra) (store : Fin (extra+64)→List Bool)
    (raw : MatchingVerification.Raw) :=
  finishResult w (prefixResult w
    (Function.update store (w 36)
      (Encoding.sequence MatchingVerification.clauseCodec (paddingRows raw.1.length)).reverse) raw)
    raw.1.length (freshRows [] raw.2).length
    (Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2)

/-- Complete canonical-source normalization, including the two forced triples,
first-occurrence deduplication, and both measured output headers. The theorem
specifies every final register and charges each emitted or copied bit. -/
theorem generator_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64)→List Bool) (raw : MatchingVerification.Raw) (flag : Bool)
    (source : store (w 0)=MatchingVerification.rawCodec.encode raw)
    (universeValue : store (w 17)=List.replicate raw.1.length true)
    (status : store (w 1)=[flag])
    (empty : ∀ i∈MatchingMachine.generatorScratch,store (w i)=[]) :
    ∃ time ≤ generatorCost (store (w 0)).length raw,
      Executes (generator extra w) store time (generatorResult w store raw) := by
  have paddingEmpty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) :
      store (paddingWorkspace w i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    all_goals simp [paddingWorkspace,paddingPositions,empty,MatchingMachine.generatorScratch]
  obtain ⟨padTime,padBound,padding⟩ := emitPadding_executes (extra+58) (paddingWorkspace w) store paddingEmpty
  let padded := Function.update store (w 36)
    (Encoding.sequence MatchingVerification.clauseCodec (paddingRows raw.1.length)).reverse
  have paddingAs : Executes (emitPadding (extra+58) (paddingWorkspace w)) store padTime padded := by
    simpa [paddingWorkspace,paddingPositions,universeValue,empty,MatchingMachine.generatorScratch,padded] using padding
  have padLimit : padTime ≤ 250*(raw.1.length+6)^2 := by
    simpa [paddingWorkspace,paddingPositions,universeValue] using padBound
  have prefixEmpty (i : Fin 64) (member : i∈normalizePrefixScratch) : padded (w i)=[] := by
    have different : i≠36 := by intro same;subst i;simp [normalizePrefixScratch] at member
    have original : i∈MatchingMachine.generatorScratch := by
      simp only [normalizePrefixScratch,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [MatchingMachine.generatorScratch]
    simp [padded,w.injective.eq_iff,different,empty i original]
  obtain ⟨prefixTime,prefixBound,prefixRun⟩ := normalizePrefix_polynomial extra w padded raw flag []
    (by simp [padded,w.injective.eq_iff,source]) (by simp [padded,w.injective.eq_iff,status]) prefixEmpty
  let prefixed := prefixResult w padded raw
  let stream := Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2
  have reversed : prefixed (w 36)=stream.reverse := by
    simp [prefixed,prefixResult,padded,w.injective.eq_iff,stream,normalizedRaw,
      rowSequence_append,List.reverse_append]
  obtain ⟨finishTime,finishBound,finishRun⟩ := finish_executes extra w prefixed raw.1.length
    (freshRows [] raw.2).length stream flag
    (by simp [prefixed,prefixResult,padded,w.injective.eq_iff,universeValue])
    (by simp [prefixed,prefixResult,padded,w.injective.eq_iff,empty,MatchingMachine.generatorScratch])
    reversed (by simp [prefixed,prefixResult,padded,w.injective.eq_iff,status])
    (by
      intro i member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl
      all_goals simp [prefixed,prefixResult,padded,w.injective.eq_iff,empty,MatchingMachine.generatorScratch])
  have combined := paddingAs.sequence (prefixRun.sequence finishRun)
  refine ⟨_,?_,combined⟩
  have prefixLimit : prefixTime ≤ 50000*((store (w 0)).length+1)^3 := by
    simpa [padded,w.injective.eq_iff] using prefixBound
  dsimp only [generatorCost]
  change finishTime ≤ finishCost raw.1.length (freshRows [] raw.2).length
    (Encoding.sequence MatchingVerification.clauseCodec (normalizedRaw raw).2).length at finishBound
  omega

theorem generatorResult_output (w : GeneratorWorkspace extra) (store : Fin (extra+64)→List Bool)
    (raw : MatchingVerification.Raw) :
    generatorResult w store raw (w 1)=MatchingVerification.rawCodec.encode (normalizedRaw raw) := by
  simp only [generatorResult,finishResult,Function.update_self,MatchingVerification.rawCodec,
    Encoding.product,Encoding.list,normalizedRaw,List.length_append,paddingRows,List.length_cons,List.length_nil]
  simp only [List.append_assoc,Nat.add_comm]

end Counting.External.CoverNormalization
