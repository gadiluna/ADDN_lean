import Counting.ExternalThreeDMEncoding

namespace Counting.External.ThreeDMEncoding

/-- A witness has one selection bit per explicitly listed edge. -/
def selected (m : Nat) (mask : List Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun j=>mask[j.val]?.getD false=true)

def maskOf {m : Nat} (chosen : Finset (Fin m)) : List Bool :=
  List.ofFn (fun j=>decide (j∈chosen))

@[simp] theorem maskOf_length {m : Nat} (chosen : Finset (Fin m)) : (maskOf chosen).length=m := by simp [maskOf]
@[simp] theorem selected_maskOf {m : Nat} (chosen : Finset (Fin m)) : selected m (maskOf chosen)=chosen := by
  ext j
  simp [selected,maskOf]

def checkMask (input : Input) (mask : List Bool) : Bool :=
  decide (mask.length=input.2.1) && (List.finRange 3).all (fun part=>(List.finRange input.1).all (fun vertex=>
    decide (((selected input.2.1 mask).filter (fun j=>input.2.2.edge j part=vertex)).card=1)))

theorem checkMask_iff (input : Input) (mask : List Bool) :
    checkMask input mask=true ↔ mask.length=input.2.1 ∧ input.2.2.IsPerfect (selected input.2.1 mask) := by
  simp [checkMask,Bool.and_eq_true,ThreeDM.IsPerfect]

theorem yes_iff_mask (input : Input) : input.2.2.Yes ↔ ∃ mask,checkMask input mask=true := by
  constructor
  · rintro ⟨chosen,perfect⟩
    exact ⟨maskOf chosen,(checkMask_iff _ _).mpr ⟨maskOf_length chosen,by simpa using perfect⟩⟩
  · rintro ⟨mask,accepted⟩
    exact ⟨selected input.2.1 mask,((checkMask_iff _ _).mp accepted).2⟩

theorem rows_count_le_stream (rows : List (List Nat)) :
    rows.length≤(Encoding.sequence (Encoding.list Encoding.natural) rows).length := by
  induction rows with
  | nil => simp [Encoding.sequence]
  | cons row rest ih =>
    have positive : 0<((Encoding.list Encoding.natural).encode row).length := by
      simp only [Encoding.list,List.length_append,Encoding.natural_length]
      omega
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    omega

theorem input_size_bounds (input : Input) : input.1≤(codec.encode input).length ∧ input.2.1≤(codec.encode input).length := by
  have rows := rows_count_le_stream ((inputTriples input).map tripleRaw)
  simp only [List.length_map,inputTriples_length] at rows
  have bits (n : Nat) : (Encoding.sequence Encoding.boolean (List.replicate n true)).length=n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ,Encoding.sequence,List.length_append,Encoding.boolean,List.length_cons,List.length_nil]
      simp only [Encoding.boolean] at ih
      omega
  have table : input.1≤((Encoding.list Encoding.boolean).encode (List.replicate input.1 true)).length := by
    simp only [Encoding.list,List.length_append,List.length_replicate,bits]
    omega
  have rest : input.2.1≤((Encoding.list (Encoding.list Encoding.natural)).encode ((inputTriples input).map tripleRaw)).length := by
    change input.2.1≤(Encoding.natural.encode _++Encoding.sequence (Encoding.list Encoding.natural) _).length
    rw [List.length_append]
    omega
  have encoded : codec.encode input=(Encoding.list Encoding.boolean).encode (List.replicate input.1 true)++
      (Encoding.list (Encoding.list Encoding.natural)).encode ((inputTriples input).map tripleRaw) := rfl
  rw [encoded,List.length_append]
  omega

def checkEncodedMask (word mask : List Bool) : Bool :=
  match codec.decodeExact word with
  | none => false
  | some input => checkMask input mask

/-- Semantic bounded-witness characterization: the mask length is bounded
by the encoded input length, and the mask satisfies the exact checker. -/
theorem matchingLanguage_iff_bounded_mask (word : List Bool) :
    word∈MatchingLanguage ↔ ∃ mask,mask.length≤word.length ∧ checkEncodedMask word mask=true := by
  constructor
  · rintro ⟨input,encoded,yes⟩
    obtain ⟨mask,accepted⟩ := (yes_iff_mask input).mp yes
    have length := ((checkMask_iff input mask).mp accepted).1
    have bounded := (input_size_bounds input).2
    have decoded := (codec.decodeExact_iff word input).mpr encoded
    refine ⟨mask,?_,?_⟩
    · rw [length,←encoded];exact bounded
    · simp [checkEncodedMask,decoded,accepted]
  · rintro ⟨mask,_bound,accepted⟩
    cases decoded : codec.decodeExact word with
    | none => simp [checkEncodedMask,decoded] at accepted
    | some input =>
      have encoded := (codec.decodeExact_iff word input).mp decoded
      exact ⟨input,encoded,(yes_iff_mask input).mpr ⟨mask,by simpa [checkEncodedMask,decoded] using accepted⟩⟩

end Counting.External.ThreeDMEncoding
