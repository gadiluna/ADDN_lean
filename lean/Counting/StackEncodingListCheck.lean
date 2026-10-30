import Counting.StackEncodingListSemantics
import Counting.StackEncodingBoundedCountSpec

namespace Counting.StackMachine.EncodingPrograms

/-- The number of iterations is capped by the remaining input length. -/
def listCount (input : List Bool) : Nat :=
  countRun (unframePayload input) 0 (unframeSuffix input).length

def listHeaderAccepted (input : List Bool) : Bool :=
  (Encoding.unframe input).isSome &&
    decide (Encoding.frame (unframePayload input)=Encoding.natural.encode (listCount input))

def listScan (input : List Bool) : ItemsResult :=
  scanItems (listCount input) (unframeSuffix input) [] (listHeaderAccepted input)

def listCheck (input : List Bool) : Bool :=
  (listScan input).accepted && decide ((listScan input).suffix=[])

theorem listCount_le (input : List Bool) : listCount input ≤ (unframeSuffix input).length := by
  simpa [listCount] using countRun_le (unframePayload input) 0 (unframeSuffix input).length

theorem natural_sequence_count (values : List Nat) :
    values.length ≤ (Encoding.sequence Encoding.natural values).length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [Encoding.sequence,List.length_append,Encoding.natural_length,List.length_cons]
    omega

theorem listHeaderAccepted_sound (input : List Bool) (accepted : listHeaderAccepted input=true) :
    input=Encoding.natural.encode (listCount input)++unframeSuffix input := by
  have both : (Encoding.unframe input).isSome=true ∧
      Encoding.frame (unframePayload input)=Encoding.natural.encode (listCount input) := by
    simpa [listHeaderAccepted] using accepted
  cases parsed : Encoding.unframe input with
  | none => simp [parsed] at both
  | some pair =>
    obtain ⟨payload,suffix⟩:=pair
    have split:=Machine.unframe_sound input payload suffix parsed
    have code := both.2
    simp only [unframePayload,parsed,Option.map_some,Option.getD_some] at code
    simp only [unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [←code]
    exact split

theorem listCheck_sound (input : List Bool) (accepted : listCheck input=true) :
    ∃ values : List Nat, (Encoding.list Encoding.natural).encode values=input := by
  have both : (listScan input).accepted=true ∧ (listScan input).suffix=[] := by
    simpa [listCheck] using accepted
  obtain ⟨header,values,length,split,_⟩:=scanItems_sound (listCount input) (unframeSuffix input) []
    (listHeaderAccepted input) both.1
  have rest : Encoding.sequence Encoding.natural values=unframeSuffix input := by
    simpa only [show (scanItems (listCount input) (unframeSuffix input) [] (listHeaderAccepted input)).suffix=[] from both.2,
      List.append_nil] using split
  refine ⟨values,?_⟩
  change Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values=input
  rw [length,rest,←listHeaderAccepted_sound input header]

theorem listScan_encode (values : List Nat) :
    listScan ((Encoding.list Encoding.natural).encode values)=
      ⟨[],(Encoding.sequence Encoding.natural values).reverse,true⟩ := by
  have parsed : Encoding.unframe ((Encoding.list Encoding.natural).encode values)=
      some (values.length.bits,Encoding.sequence Encoding.natural values) := Encoding.unframe_frame _ _
  have count : listCount ((Encoding.list Encoding.natural).encode values)=values.length := by
    simp only [listCount,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right (natural_sequence_count values)]
  have status : listHeaderAccepted ((Encoding.list Encoding.natural).encode values)=true := by
    simp only [listHeaderAccepted,parsed,unframePayload,count,Option.isSome_some,Option.map_some,Option.getD_some]
    simp [Encoding.natural]
  simp only [listScan,count,status,unframeSuffix,parsed,Option.map_some,Option.getD_some]
  simpa only [List.append_nil] using scanItems_naturals values [] []

theorem listScan_append (values : List Nat) (suffix : List Bool) :
    listScan ((Encoding.list Encoding.natural).encode values++suffix)=
      ⟨suffix,(Encoding.sequence Encoding.natural values).reverse,true⟩ := by
  have parsed : Encoding.unframe ((Encoding.list Encoding.natural).encode values++suffix)=
      some (values.length.bits,Encoding.sequence Encoding.natural values++suffix) := by
    change Encoding.unframe ((Encoding.frame values.length.bits++Encoding.sequence Encoding.natural values)++suffix)=_
    rw [List.append_assoc,Encoding.unframe_frame]
  have count : listCount ((Encoding.list Encoding.natural).encode values++suffix)=values.length := by
    simp only [listCount,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right]
    simpa only [List.length_append] using (natural_sequence_count values).trans (Nat.le_add_right _ _)
  have status : listHeaderAccepted ((Encoding.list Encoding.natural).encode values++suffix)=true := by
    simp only [listHeaderAccepted,parsed,unframePayload,count,Option.isSome_some,Option.map_some,Option.getD_some]
    simp [Encoding.natural]
  simp only [listScan,count,status,unframeSuffix,parsed,Option.map_some,Option.getD_some]
  simpa only [List.append_nil] using scanItems_naturals values suffix []

theorem listScan_sound (input : List Bool) (accepted : (listScan input).accepted=true) :
    ∃ values : List Nat, (Encoding.list Encoding.natural).encode values++(listScan input).suffix=input ∧
      (listScan input).reversed=(Encoding.sequence Encoding.natural values).reverse := by
  obtain ⟨header,values,length,split,output⟩:=scanItems_sound (listCount input) (unframeSuffix input) []
    (listHeaderAccepted input) accepted
  refine ⟨values,?_,by simpa only [listScan,List.append_nil] using output⟩
  change (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++_=input
  rw [length,List.append_assoc,listScan,split,←listHeaderAccepted_sound input header]

theorem listScan_accept_iff (input : List Bool) :
    (listScan input).accepted=true ↔
      ∃ values : List Nat, ∃ suffix, (Encoding.list Encoding.natural).encode values++suffix=input := by
  constructor
  · intro accepted
    obtain ⟨values,split,_⟩:=listScan_sound input accepted
    exact ⟨values,_,split⟩
  · rintro ⟨values,suffix,rfl⟩
    rw [listScan_append]

theorem listCheck_encode (values : List Nat) :
    listCheck ((Encoding.list Encoding.natural).encode values)=true := by
  simp [listCheck,listScan_encode]

/-- Exact agreement on every bit string, including oversized or noncanonical
length headers, truncated fields, redundant zero bits and trailing data. -/
theorem listCheck_decodeExact (input : List Bool) :
    listCheck input=((Encoding.list Encoding.natural).decodeExact input).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    obtain ⟨values,equal⟩:=listCheck_sound input accepted
    rw [(Encoding.Codec.decodeExact_iff _ input values).mpr equal]
    rfl
  · intro accepted
    obtain ⟨values,decoded⟩:=Option.isSome_iff_exists.mp accepted
    have equal := (Encoding.Codec.decodeExact_iff _ input values).mp decoded
    rw [←equal,listCheck_encode]

theorem scanItems_lengths (count : Nat) (input reversed : List Bool) (accepted : Bool) :
    (scanItems count input reversed accepted).suffix.length≤ input.length ∧
      (scanItems count input reversed accepted).reversed.length≤
        reversed.length+count*(2*input.length+1) := by
  induction count generalizing input reversed accepted with
  | zero => simp [scanItems]
  | succ count ih =>
    obtain ⟨suffixBound,outputBound⟩:=ih (unframeSuffix input)
      ((Encoding.frame (unframePayload input)).reverse++reversed) (accepted && itemAccepted input)
    have suffix := unframe_suffix_length input
    have payload := unframe_payload_length input
    change _≤ input.length ∧ _≤_
    refine ⟨suffixBound.trans suffix,?_⟩
    simp only [List.length_append,List.length_reverse,Encoding.frame_length] at outputBound
    have product := Nat.mul_le_mul_left count (show 2*(unframeSuffix input).length+1≤2*input.length+1 by omega)
    simp only [scanItems]
    nlinarith

end Counting.StackMachine.EncodingPrograms
