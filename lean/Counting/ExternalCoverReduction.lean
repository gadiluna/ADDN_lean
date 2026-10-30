import Counting.ExternalMatchingCoverEncoding
import Counting.ExternalMatchingReduction

namespace Counting.External.CoverMachine

def rejectCover : X3CEncoding.Input := ThreeDMEncoding.coverInput MatchingMachine.rejectMatching

theorem rejectCover_no : ¬∃ chosen,rejectCover.2.2.IsExactCover chosen := by
  rw [rejectCover,ThreeDMEncoding.coverInput_yes_iff]
  exact MatchingMachine.rejectMatching_no

def reduceCover (word : List Bool) : List Bool :=
  match ThreeDMEncoding.codec.decodeExact word with
  | none => X3CEncoding.codec.encode rejectCover
  | some input => X3CEncoding.codec.encode (ThreeDMEncoding.coverInput input)

theorem reduceCover_encoded (input : ThreeDMEncoding.Input) :
    reduceCover (ThreeDMEncoding.codec.encode input)=X3CEncoding.codec.encode (ThreeDMEncoding.coverInput input) := by
  have decoded := (ThreeDMEncoding.codec.decodeExact_iff _ input).mpr rfl
  simp only [reduceCover,decoded]

theorem reduceCover_yes_iff (word : List Bool) :
    X3CEncoding.BinaryX3C (reduceCover word) ↔ word∈ThreeDMEncoding.MatchingLanguage := by
  have rejected : ¬X3CEncoding.BinaryX3C (X3CEncoding.codec.encode rejectCover) := by
    rw [X3CEncoding.encoded_yes_iff]
    exact rejectCover_no
  cases decoded : ThreeDMEncoding.codec.decodeExact word with
  | none =>
    have absent : ¬word∈ThreeDMEncoding.MatchingLanguage := by
      rintro ⟨input,encoded,_⟩
      have present := (ThreeDMEncoding.codec.decodeExact_iff word input).mpr encoded
      rw [decoded] at present
      cases present
    simp [reduceCover,decoded,absent,rejected]
  | some input =>
    have encoded := (ThreeDMEncoding.codec.decodeExact_iff word input).mp decoded
    rw [←encoded,reduceCover_encoded,X3CEncoding.encoded_yes_iff,
      ThreeDMEncoding.coverInput_yes_iff,ThreeDMEncoding.encoded_yes_iff]

end Counting.External.CoverMachine
