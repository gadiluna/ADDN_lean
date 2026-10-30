import Counting.StackEncodingIncomingMachine

namespace Counting.StackMachine.EncodingPrograms

def incomingInputCodec : Encoding.Codec (Nat × List (Nat × Nat)) :=
  Encoding.product Encoding.natural (Encoding.list (Encoding.product Encoding.natural Encoding.natural))

/-- The exact language accepted by the physical machine, including rejection
of every noncanonical or malformed serialization. -/
theorem incomingEncodedCheck_iff (input : List Bool) :
    incomingEncodedCheck input=true ↔ ∃ bound edges,
      incomingInputCodec.encode (bound,edges)=input ∧
      Executable.countsSorted edges=true ∧ edges.all (fun edge=>decide (edge.1<bound))=true := by
  constructor
  · intro accepted
    let result:=incomingPrefixResult (unframePayload input) (unframeSuffix input) [] true (itemAccepted input)
    have both : result.accepted=true ∧ result.suffix=[] := by
      simpa only [incomingEncodedCheck,Bool.and_eq_true,decide_eq_true_eq] using accepted
    obtain ⟨boundValid,edges,split,checked⟩:=incomingPrefix_sound (unframePayload input) (unframeSuffix input) [] true
      (itemAccepted input) both.1
    have boundSplit:=itemAccepted_sound input boundValid
    have edgeCode : (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges=unframeSuffix input := by
      simpa only [show (incomingPrefixResult (unframePayload input) (unframeSuffix input) [] true (itemAccepted input)).suffix=[] from both.2,
        List.append_nil] using split
    refine ⟨Encoding.value (unframePayload input),edges,?_,?_⟩
    · change Encoding.natural.encode _++(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges=input
      rw [edgeCode,←boundSplit.1]
    · apply (incomingCheck_iff _ _).mp
      simpa only [incomingPrevious,↓reduceIte] using checked
  · rintro ⟨bound,edges,rfl,sorted,inside⟩
    let encoded:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges
    have parsed : Encoding.unframe (incomingInputCodec.encode (bound,edges))=some (bound.bits,encoded) :=
      Encoding.unframe_frame _ _
    have payload : unframePayload (incomingInputCodec.encode (bound,edges))=bound.bits := by
      simp [unframePayload,parsed]
    have suffix : unframeSuffix (incomingInputCodec.encode (bound,edges))=encoded := by
      simp [unframeSuffix,parsed]
    have accepted : itemAccepted (incomingInputCodec.encode (bound,edges))=true := by
      simp only [itemAccepted,parsed,Option.isSome_some,Bool.true_and,payload]
      exact (canonicalPayload_iff _).mpr (by rw [Encoding.value_bits])
    have valid : incomingCheck (Encoding.value bound.bits) (incomingPrevious [] true) edges=true := by
      simpa only [Encoding.value_bits,incomingPrevious,↓reduceIte] using (incomingCheck_iff bound edges).mpr ⟨sorted,inside⟩
    have complete : (incomingPrefixResult bound.bits encoded [] true true).accepted=true := by
      simpa only [List.append_nil] using incomingPrefix_complete bound.bits [] true edges [] valid
    obtain ⟨_,other,split,_⟩:=incomingPrefix_sound bound.bits encoded [] true true complete
    let codec:=Encoding.list (Encoding.product Encoding.natural Encoding.natural)
    have decoded : some (other,(incomingPrefixResult bound.bits encoded [] true true).suffix)=some (edges,[]) := by
      calc
        _=codec.decode (codec.encode other++(incomingPrefixResult bound.bits encoded [] true true).suffix) :=
          (codec.roundtrip _ _).symm
        _=codec.decode encoded := congrArg codec.decode split
        _=some (edges,[]) := by simpa only [List.append_nil] using codec.roundtrip edges []
    have exhausted : (incomingPrefixResult bound.bits encoded [] true true).suffix=[] :=
      congrArg Prod.snd (Option.some.inj decoded)
    simp only [incomingEncodedCheck,payload,suffix,accepted,complete,Bool.true_and,exhausted,decide_true]

theorem incomingEncodedCheck_encode (bound : Nat) (edges : List (Nat × Nat)) :
    incomingEncodedCheck (incomingInputCodec.encode (bound,edges))=
      (Executable.countsSorted edges && edges.all (fun edge=>decide (edge.1<bound))) := by
  apply Bool.eq_iff_iff.mpr
  rw [incomingEncodedCheck_iff,Bool.and_eq_true]
  constructor
  · rintro ⟨bound',edges',equal,sorted,inside⟩
    have same:=incomingInputCodec.injective equal
    cases same
    exact ⟨sorted,inside⟩
  · rintro ⟨sorted,inside⟩
    exact ⟨bound,edges,rfl,sorted,inside⟩

theorem incomingEncodedCheck_invalid (input : List Bool) (invalid : incomingInputCodec.decodeExact input=none) :
    incomingEncodedCheck input=false := by
  cases h : incomingEncodedCheck input with
  | false => rfl
  | true =>
      obtain ⟨bound,edges,code,_,_⟩:=(incomingEncodedCheck_iff input).mp h
      have decoded:incomingInputCodec.decodeExact input=some (bound,edges) :=
        (Encoding.Codec.decodeExact_iff _ input _).mpr code
      rw [invalid] at decoded
      contradiction

end Counting.StackMachine.EncodingPrograms
