import Counting.StackEncodingIncomingScan
import Counting.StackEncodingListCheck
import Counting.StackEncodingParserMany

namespace Counting.StackMachine.EncodingPrograms

def incomingPrefixResult (bound input previous : List Bool) (first accepted : Bool) : IncomingScanResult :=
  scanIncoming bound (listCount input) (unframeSuffix input) previous first (accepted && listHeaderAccepted input)

theorem incomingPrefix_sound (bound input previous : List Bool) (first accepted : Bool)
    (valid : (incomingPrefixResult bound input previous first accepted).accepted=true) :
    accepted=true ∧ ∃ edges : List (Nat × Nat),
      (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++
        (incomingPrefixResult bound input previous first accepted).suffix=input ∧
      incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges=true := by
  have start:=scanIncoming_status bound (listCount input) (unframeSuffix input) previous first
    (accepted && listHeaderAccepted input) valid
  have flags : accepted=true ∧ listHeaderAccepted input=true := by simpa only [Bool.and_eq_true] using start
  obtain ⟨edges,length,split,checked⟩:=scanIncoming_sound bound (listCount input) (unframeSuffix input)
    previous first (accepted && listHeaderAccepted input) valid
  refine ⟨flags.1,edges,?_,checked⟩
  change (Encoding.natural.encode edges.length++Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges)++_=input
  rw [length,List.append_assoc,incomingPrefixResult,split,←listHeaderAccepted_sound input flags.2]

theorem incomingPrefix_complete (bound previous : List Bool) (first : Bool)
    (edges : List (Nat × Nat)) (suffix : List Bool)
    (valid : incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges=true) :
    (incomingPrefixResult bound
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix)
      previous first true).accepted=true := by
  let codec:=Encoding.product Encoding.natural Encoding.natural
  let input:=(Encoding.list codec).encode edges++suffix
  have parsed : Encoding.unframe input=some (edges.length.bits,Encoding.sequence codec edges++suffix) := by
    change Encoding.unframe ((Encoding.frame edges.length.bits++Encoding.sequence codec edges)++suffix)=_
    rw [List.append_assoc,Encoding.unframe_frame]
  have positive (edge : Nat × Nat) : 0<(codec.encode edge).length := by
    simp only [codec,Encoding.product,List.length_append,Encoding.natural_length]
    omega
  have count : listCount input=edges.length := by
    simp only [listCount,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right]
    have countBound:=VerifiedParser.sequence_count_le positive edges
    simpa only [List.length_append] using countBound.trans (Nat.le_add_right _ _)
  have header : listHeaderAccepted input=true := by
    simp only [listHeaderAccepted,unframePayload,parsed,count,Option.map_some,Option.getD_some,Option.isSome_some]
    simp [Encoding.natural]
  change (incomingPrefixResult bound input previous first true).accepted=true
  simp only [incomingPrefixResult,count,header,Bool.true_and,unframeSuffix,parsed,Option.map_some,Option.getD_some]
  exact scanIncoming_complete bound previous first edges suffix valid

/-- Canonical prefix recognition together with the graph conditions, with no
promise about the input word. -/
theorem incomingPrefix_accept_iff (bound input previous : List Bool) (first : Bool) :
    (incomingPrefixResult bound input previous first true).accepted=true ↔
      ∃ edges : List (Nat × Nat),∃ suffix,
        (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix=input ∧
        incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges=true := by
  constructor
  · intro accepted
    obtain ⟨_,edges,split,checked⟩:=incomingPrefix_sound bound input previous first true accepted
    exact ⟨edges,_,split,checked⟩
  · rintro ⟨edges,suffix,rfl,valid⟩
    exact incomingPrefix_complete bound previous first edges suffix valid

end Counting.StackMachine.EncodingPrograms
