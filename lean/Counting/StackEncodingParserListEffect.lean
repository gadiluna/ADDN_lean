import Counting.StackEncodingParserMany

namespace Counting.StackMachine.EncodingPrograms

def listEffect (effect : List Bool → ParseEffect) (input : List Bool) : ParseEffect :=
  let items := manyEffect effect (listCount input) (unframeSuffix input)
  ⟨items.suffix,Encoding.frame (unframePayload input)++items.code,listHeaderAccepted input && items.accepted⟩

namespace VerifiedParser

variable {registers : Nat} {source status output : Fin (registers+2)}
  {α : Type} {codec : Encoding.Codec α}
  (parser : VerifiedParser registers source status output α codec)

theorem list_effect_suffix (input : List Bool) :
    (listEffect parser.effect input).suffix.length≤ input.length :=
  (parser.many_suffix_le _ _).trans (unframe_suffix_length input)

theorem list_effect_sound (input : List Bool) (accepted : (listEffect parser.effect input).accepted=true) :
    ∃ values : List α, (Encoding.list codec).encode values++(listEffect parser.effect input).suffix=input ∧
      (listEffect parser.effect input).code=(Encoding.list codec).encode values := by
  have both : listHeaderAccepted input=true ∧
      (manyEffect parser.effect (listCount input) (unframeSuffix input)).accepted=true := by
    simpa only [listEffect,Bool.and_eq_true] using accepted
  obtain ⟨values,length,split,code⟩:=parser.many_sound _ _ both.2
  have header := listHeaderAccepted_sound input both.1
  have headerCode : Encoding.frame (unframePayload input)=Encoding.natural.encode (listCount input) := by
    have h : (Encoding.unframe input).isSome=true ∧
        Encoding.frame (unframePayload input)=Encoding.natural.encode (listCount input) := by
      simpa [listHeaderAccepted] using both.1
    exact h.2
  refine ⟨values,?_,?_⟩
  · change (Encoding.natural.encode values.length++Encoding.sequence codec values)++_=input
    rw [listEffect,List.append_assoc,split,length,←header]
  · simp only [listEffect,code,headerCode,Encoding.list,length]

theorem list_effect_roundtrip (positive : ∀ value,0<(codec.encode value).length)
    (values : List α) (suffix : List Bool) :
    listEffect parser.effect ((Encoding.list codec).encode values++suffix)=
      ⟨suffix,(Encoding.list codec).encode values,true⟩ := by
  let input := (Encoding.list codec).encode values++suffix
  have parsed : Encoding.unframe input=some (values.length.bits,Encoding.sequence codec values++suffix) := by
    change Encoding.unframe ((Encoding.frame values.length.bits++Encoding.sequence codec values)++suffix)=_
    rw [List.append_assoc,Encoding.unframe_frame]
  have count : listCount input=values.length := by
    simp only [listCount,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right]
    have countBound:=sequence_count_le positive values
    simpa only [List.length_append] using countBound.trans (Nat.le_add_right _ _)
  have header : listHeaderAccepted input=true := by
    simp only [listHeaderAccepted,unframePayload,parsed,count,Option.map_some,Option.getD_some,Option.isSome_some]
    simp [Encoding.natural]
  change listEffect parser.effect input=_
  simp only [listEffect,header,count,unframeSuffix,unframePayload,parsed,Option.map_some,Option.getD_some,
    parser.many_roundtrip,Bool.true_and]
  rfl

theorem list_effect_code_bound (input : List Bool) :
    (listEffect parser.effect input).code.length ≤
      Complexity.polynomial (parser.coefficient+3) (parser.exponent+1) input.length := by
  have items:=parser.many_code_le (listCount input) (unframeSuffix input)
  have countBound:=(listCount_le input).trans (unframe_suffix_length input)
  have suffixBound:=unframe_suffix_length input
  have payloadBound:=unframe_payload_length input
  have polynomial : Complexity.polynomial parser.coefficient parser.exponent (unframeSuffix input).length ≤
      Complexity.polynomial parser.coefficient parser.exponent input.length := by
    unfold Complexity.polynomial
    gcongr
  have product := Nat.mul_le_mul countBound polynomial
  have positive : 1≤(input.length+1)^parser.exponent := Nat.one_le_pow _ _ (by omega)
  simp only [listEffect,List.length_append,Encoding.frame_length,Complexity.polynomial,pow_succ]
  unfold Complexity.polynomial at items product
  nlinarith

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
