import Counting.ExternalMatchingWitness
import Counting.X3CEncoding

namespace Counting.External.CoverVerification
open ThreeDMEncoding

def checkMask (input : X3CEncoding.Input) (mask : List Bool) : Bool :=
  decide (mask.length=input.2.1) && (List.finRange (3*input.1)).all (fun element=>
    decide (((selected input.2.1 mask).filter (fun j=>element∈input.2.2.triples j)).card=1))

theorem checkMask_iff (input : X3CEncoding.Input) (mask : List Bool) :
    checkMask input mask=true ↔ mask.length=input.2.1 ∧ input.2.2.IsExactCover (selected input.2.1 mask) := by
  simp [checkMask,Bool.and_eq_true,X3C.RawInstance.IsExactCover]

theorem yes_iff_mask (input : X3CEncoding.Input) :
    (∃ chosen,input.2.2.IsExactCover chosen) ↔ ∃ mask,checkMask input mask=true := by
  constructor
  · rintro ⟨chosen,cover⟩
    exact ⟨maskOf chosen,(checkMask_iff _ _).mpr ⟨maskOf_length chosen,by simpa using cover⟩⟩
  · rintro ⟨mask,accepted⟩
    exact ⟨selected input.2.1 mask,((checkMask_iff input mask).mp accepted).2⟩

def checkEncodedMask (word mask : List Bool) : Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none => false
  | some input => checkMask input mask

/-- Semantic certificate length. The physical verifier is developed separately. -/
theorem binaryX3C_iff_bounded_mask (word : List Bool) :
    X3CEncoding.BinaryX3C word ↔ ∃ mask,mask.length≤word.length ∧ checkEncodedMask word mask=true := by
  constructor
  · rintro ⟨input,decoded,yes⟩
    have encoded := (X3CEncoding.codec.decodeExact_iff word input).mp decoded
    obtain ⟨mask,accepted⟩ := (yes_iff_mask input).mp yes
    have length := ((checkMask_iff input mask).mp accepted).1
    have bounded := (X3CEncoding.input_size_bounds input).2
    refine ⟨mask,?_,?_⟩
    · rw [length,←encoded];exact bounded
    · simp [checkEncodedMask,decoded,accepted]
  · rintro ⟨mask,_bound,accepted⟩
    cases decoded : X3CEncoding.codec.decodeExact word with
    | none => simp [checkEncodedMask,decoded] at accepted
    | some input =>
      exact ⟨input,decoded,(yes_iff_mask input).mpr ⟨mask,by simpa [checkEncodedMask,decoded] using accepted⟩⟩

end Counting.External.CoverVerification
