import Counting.StackEncodingListItem

namespace Counting.StackMachine.EncodingPrograms

structure ItemsResult where
  suffix : List Bool
  reversed : List Bool
  accepted : Bool
  deriving Repr, DecidableEq

def scanItems : Nat → List Bool → List Bool → Bool → ItemsResult
  | 0,input,reversed,accepted => ⟨input,reversed,accepted⟩
  | count+1,input,reversed,accepted =>
    scanItems count (unframeSuffix input)
      ((Encoding.frame (unframePayload input)).reverse++reversed) (accepted && itemAccepted input)

theorem unframe_suffix_length (input : List Bool) : (unframeSuffix input).length ≤ input.length := by
  cases parsed : Encoding.unframe input with
  | none => simp [unframeSuffix,parsed]
  | some pair =>
    obtain ⟨payload,suffix⟩:=pair
    have split:=Machine.unframe_sound input payload suffix parsed
    simp only [unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [split,List.length_append]
    omega

theorem itemAccepted_sound (input : List Bool) (accepted : itemAccepted input=true) :
    input=Encoding.natural.encode (Encoding.value (unframePayload input))++unframeSuffix input ∧
      Encoding.frame (unframePayload input)=Encoding.natural.encode (Encoding.value (unframePayload input)) := by
  cases parsed : Encoding.unframe input with
  | none => simp [itemAccepted,parsed] at accepted
  | some pair =>
    obtain ⟨payload,suffix⟩:=pair
    have split:=Machine.unframe_sound input payload suffix parsed
    have canonical : canonicalPayload payload=true := by
      simpa [itemAccepted,unframePayload,parsed] using accepted
    have exactBits := (canonicalPayload_iff payload).mp canonical
    simp only [unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    change input=Encoding.frame (Encoding.value payload).bits++suffix ∧
      Encoding.frame payload=Encoding.frame (Encoding.value payload).bits
    rw [←exactBits]
    exact ⟨split,rfl⟩

theorem scanItems_sound (count : Nat) (input reversed : List Bool) (accepted : Bool)
    (valid : (scanItems count input reversed accepted).accepted=true) :
    accepted=true ∧ ∃ values : List Nat, values.length=count ∧
      Encoding.sequence Encoding.natural values++(scanItems count input reversed accepted).suffix=input ∧
      (scanItems count input reversed accepted).reversed=
        (Encoding.sequence Encoding.natural values).reverse++reversed := by
  induction count generalizing input reversed accepted with
  | zero => exact ⟨valid,[],rfl,rfl,rfl⟩
  | succ count ih =>
    obtain ⟨nextValid,values,length,split,output⟩ := ih (unframeSuffix input)
      ((Encoding.frame (unframePayload input)).reverse++reversed) (accepted && itemAccepted input) valid
    have both : accepted=true ∧ itemAccepted input=true := by simpa only [Bool.and_eq_true] using nextValid
    obtain ⟨initialValid,itemValid⟩ := both
    obtain ⟨firstSplit,firstCode⟩ := itemAccepted_sound input itemValid
    refine ⟨initialValid,Encoding.value (unframePayload input)::values,by simp [length],?_,?_⟩
    · change Encoding.natural.encode (Encoding.value (unframePayload input))++Encoding.sequence Encoding.natural values++_ = _
      rw [scanItems,List.append_assoc,split,←firstSplit]
    · change (scanItems count _ _ _).reversed = _
      rw [output,Encoding.sequence,List.reverse_append,←firstCode,List.append_assoc]

theorem scanItems_naturals (values : List Nat) (suffix reversed : List Bool) :
    scanItems values.length (Encoding.sequence Encoding.natural values++suffix) reversed true =
      ⟨suffix,(Encoding.sequence Encoding.natural values).reverse++reversed,true⟩ := by
  induction values generalizing reversed with
  | nil => rfl
  | cons value values ih =>
    have canonical : canonicalPayload value.bits=true := (canonicalPayload_iff value.bits).mpr (by rw [Encoding.value_bits])
    simp only [List.length_cons,Encoding.sequence,List.append_assoc,scanItems]
    have parsed : Encoding.unframe (Encoding.natural.encode value++(Encoding.sequence Encoding.natural values++suffix)) =
        some (value.bits,Encoding.sequence Encoding.natural values++suffix) := Encoding.unframe_frame _ _
    simp only [unframeSuffix,unframePayload,itemAccepted,parsed,Option.map_some,Option.getD_some,
      Option.isSome_some,canonical,Bool.true_and]
    rw [ih]
    simp only [List.reverse_append,List.append_assoc]
    rfl

theorem scanItems_accept_iff (count : Nat) (input : List Bool) :
    (scanItems count input [] true).accepted=true ↔
      ∃ values : List Nat, values.length=count ∧ ∃ suffix,
        Encoding.sequence Encoding.natural values++suffix=input := by
  constructor
  · intro accepted
    obtain ⟨_,values,length,split,_⟩ := scanItems_sound count input [] true accepted
    exact ⟨values,length,_,split⟩
  · rintro ⟨values,rfl,suffix,rfl⟩
    rw [scanItems_naturals]

end Counting.StackMachine.EncodingPrograms
