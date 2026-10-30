import Counting.ExternalCoverNormalizeLoop
import Counting.ExternalCoverPrepare

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def normalizePrefixScratch : List (Fin 64) :=
  [2,3,4,5,6,9,10,11,12,13,14,18,20,22,23,24,29,30,38,39,40,43,44,52]

def normalizePrefix (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (coverPrepare extra w)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 0) (w 39) (w 44)))
      (dedupRows (extra+16) w.literal))

def prefixResult (w : GeneratorWorkspace extra) (store : Fin (extra+64)→List Bool)
    (raw : MatchingVerification.Raw) :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 0) []) (w 23) [])
    (w 39) (Encoding.sequence MatchingVerification.clauseCodec raw.2))
    (w 36) ((Encoding.sequence MatchingVerification.clauseCodec (freshRows [] raw.2)).reverse++store (w 36)))
    (w 41) (List.replicate (freshRows [] raw.2).length true++store (w 41)))
    (w 40) (List.replicate raw.2.length true)

/-- Parse both input headers, skip the actual explicit universe, copy the
original row stream and deduplicate it. The row count is obtained from the
encoded input by the charged parser, not supplied as a free list length. -/
theorem normalizePrefix_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64)→List Bool) (raw : MatchingVerification.Raw)
    (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=MatchingVerification.rawCodec.encode raw)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈normalizePrefixScratch,store (w i)=[]) :
    ∃ time ≤ 4000*((store (w 0)).length+raw.1.length+1)^3+
        5*(Encoding.sequence MatchingVerification.clauseCodec raw.2).length+
        raw.2.length*(2000*(2*(Encoding.sequence MatchingVerification.clauseCodec raw.2).length+1)^2+2)+5,
      Executes (normalizePrefix extra w) store time (prefixResult w store raw) := by
  have prepEmpty (i : Fin 64) (member : i∈coverPrepareScratch) : store (w i)=[] := by
    apply empty
    simp only [coverPrepareScratch,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  obtain ⟨prepTime,prepBound,preparing⟩ := coverPrepare_executes extra w store
    (MatchingVerification.toRaw raw) accepted tail (by rw [source,MatchingVerification.rawCodec_encode]) status prepEmpty
  let stream := Encoding.sequence MatchingVerification.clauseCodec raw.2
  have streamAs : Encoding.sequence (Encoding.list Encoding.natural)
      (raw.2.map MatchingVerification.clauseToRaw)=stream :=
    (MatchingVerification.sequence_encode raw.2).symm
  let prepared := Function.update (Function.update store (w 0) stream) (w 23) (List.replicate raw.2.length true)
  have prepAs : Executes (coverPrepare extra w) store prepTime prepared := by
    simpa only [MatchingVerification.toRaw,List.length_map,streamAs,prepared] using preparing
  have copying := copy_executes (extra+61) (w 0) (w 39) (w 44)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) prepared
    (by simp [prepared,w.injective.eq_iff,empty,normalizePrefixScratch])
  let copied := Function.update prepared (w 39) stream
  have copyAs : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 0) (w 39) (w 44)))
      prepared (5*stream.length+2) copied := by
    simpa +instances [copied,prepared,w.injective.eq_iff,empty,normalizePrefixScratch] using copying
  have loopEmpty (i : Fin 48) (member : i∈stepScratch) : copied (w.literal i)=[] := by
    simp only [stepScratch,previousScratch,matchScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with ((rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl))|rfl
    all_goals simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,empty,normalizePrefixScratch]
  obtain ⟨loopTime,loopBound,looping⟩ := dedupRows_executes (extra+16) w.literal [] raw.2
    (2*stream.length+1) copied accepted tail []
    (by simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,stream])
    (by simp [copied,GeneratorWorkspace.literal,literalPositions,stream])
    (by simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff])
    (by simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,empty,normalizePrefixScratch])
    (by simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,status])
    (by simp [copied,prepared,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff];omega) loopEmpty
  have final : dedupResult w.literal copied [] raw.2 []=prefixResult w store raw := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [dedupResult,prefixResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff]
    · by_cases e23 : r=w 23
      · subst r;simp [dedupResult,prefixResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff]
      · by_cases e40 : r=w 40
        · subst r;simp [dedupResult,prefixResult,copied,prepared,GeneratorWorkspace.literal,literalPositions,
            w.injective.eq_iff,empty,normalizePrefixScratch]
        · simp [dedupResult,prefixResult,copied,prepared,GeneratorWorkspace.literal,literalPositions,
            e0,e23,e40,Function.update_apply,w.injective.eq_iff,stream]
  rw [final] at looping
  refine ⟨prepTime+1+(5*stream.length+2+1+loopTime),?_,prepAs.sequence (copyAs.sequence looping)⟩
  change prepTime ≤ 4000*((store (w 0)).length+raw.1.length+1)^3 at prepBound
  change _ ≤ 4000*((store (w 0)).length+raw.1.length+1)^3+5*stream.length+
    raw.2.length*(2000*(2*stream.length+1)^2+2)+5
  omega

end Counting.External.CoverNormalization
