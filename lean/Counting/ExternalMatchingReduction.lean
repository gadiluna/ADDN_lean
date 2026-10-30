import Counting.ExternalThreeSATTyped

namespace Counting.External.MatchingMachine
open CNFMachine

def rejectMatching : ThreeDMEncoding.Input := ⟨1,0,⟨fun j=>Fin.elim0 j⟩⟩

theorem rejectMatching_no : ¬rejectMatching.2.2.Yes := by
  rintro ⟨chosen,perfect⟩
  have h := perfect (0 : Fin 3) (⟨0,by decide⟩ : Fin 1)
  have empty : chosen=∅ := Finset.eq_empty_of_forall_notMem (fun j=>Fin.elim0 j)
  simp [empty] at h

def reduceMatching (input : List Bool) : List Bool :=
  match CNFEncoding.codec.decodeExact input with
  | none => ThreeDMEncoding.codec.encode rejectMatching
  | some formula =>
    if three : ∀ clause∈formula.2,clause.length=3 then
      ThreeDMEncoding.codec.encode (asThreeSAT formula three).sparseInput
    else ThreeDMEncoding.codec.encode rejectMatching

theorem reduceMatching_encoded (formula : CNFInput) (three : ∀ clause∈formula.2,clause.length=3) :
    reduceMatching (CNFEncoding.codec.encode formula)=ThreeDMEncoding.codec.encode (asThreeSAT formula three).sparseInput := by
  have decoded := (Encoding.Codec.decodeExact_iff CNFEncoding.codec _ formula).mpr rfl
  simp only [reduceMatching,decoded]
  rw [dif_pos three]

theorem reduceMatching_yes_iff (input : List Bool) :
    reduceMatching input∈ThreeDMEncoding.MatchingLanguage ↔ input∈ThreeSATLanguage := by
  have rejected : ¬ThreeDMEncoding.codec.encode rejectMatching∈ThreeDMEncoding.MatchingLanguage := by
    rw [ThreeDMEncoding.encoded_yes_iff]
    exact rejectMatching_no
  cases decoded : CNFEncoding.codec.decodeExact input with
  | none =>
    have absent : ¬input∈ThreeSATLanguage := by
      rintro ⟨formula,encoded,_⟩
      have present := (Encoding.Codec.decodeExact_iff CNFEncoding.codec input formula).mpr encoded
      rw [decoded] at present
      cases present
    simp [reduceMatching,decoded,absent,rejected]
  | some formula =>
    have encoded := (Encoding.Codec.decodeExact_iff CNFEncoding.codec input formula).mp decoded
    by_cases three : ∀ clause∈formula.2,clause.length=3
    · rw [←encoded,reduceMatching_encoded formula three,ThreeDMEncoding.encoded_yes_iff,
        ThreeSAT.sparseInput_yes_iff,asThreeSAT_yes_iff,ThreeSATLanguage,Complexity.encodedLanguage_iff]
      exact (and_iff_right three).symm
    · have absent : ¬input∈ThreeSATLanguage := by
        rw [←encoded,ThreeSATLanguage,Complexity.encodedLanguage_iff]
        exact fun satisfied=>three satisfied.1
      simp [reduceMatching,decoded,three,absent,rejected]

end Counting.External.MatchingMachine
