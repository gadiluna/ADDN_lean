import Counting.StackEncodingIncomingSpec
import Counting.StackEncodingListSemantics

namespace Counting.StackMachine.EncodingPrograms

structure IncomingScanResult where
  suffix : List Bool
  previous : List Bool
  first : Bool
  accepted : Bool
  deriving Repr,DecidableEq

def scanIncoming (bound : List Bool) : Nat → List Bool → List Bool → Bool → Bool → IncomingScanResult
  | 0,input,previous,first,accepted => ⟨input,previous,first,accepted⟩
  | count+1,input,previous,first,accepted =>
      let parsed:=parsePair input
      scanIncoming bound count parsed.suffix parsed.first false
        (accepted && incomingPayloadCheck bound previous first parsed)

def incomingPrevious (previous : List Bool) (first : Bool) : Option Nat :=
  if first then none else some (Encoding.value previous)

theorem incoming_parsePair_accepted (input : List Bool) (accepted : (parsePair input).accepted=true) :
    Encoding.frame (parsePair input).first++Encoding.frame (parsePair input).second++(parsePair input).suffix=input := by
  cases h1 : Encoding.unframe input with
  | none => simp [parsePair,h1] at accepted
  | some pair =>
      rcases pair with ⟨first,rest⟩
      cases h2 : Encoding.unframe rest with
      | none => simp [parsePair,h1,h2] at accepted
      | some pair =>
          rcases pair with ⟨second,suffix⟩
          have a:=Machine.unframe_sound input first rest h1
          have b:=Machine.unframe_sound rest second suffix h2
          simpa [parsePair,h1,h2,List.append_assoc,b] using a.symm

theorem scanIncoming_status (bound : List Bool) (count : Nat) (input previous : List Bool) (first accepted : Bool) :
    (scanIncoming bound count input previous first accepted).accepted=true → accepted=true := by
  induction count generalizing input previous first accepted with
  | zero => exact id
  | succ count ih =>
      intro result
      have h:=ih _ _ _ _ result
      have both : accepted=true ∧ incomingPayloadCheck bound previous first (parsePair input)=true := by
        simpa only [Bool.and_eq_true] using h
      exact both.1

theorem scanIncoming_suffix_le (bound : List Bool) (count : Nat) (input previous : List Bool) (first accepted : Bool) :
    (scanIncoming bound count input previous first accepted).suffix.length≤ input.length := by
  induction count generalizing input previous first accepted with
  | zero => exact le_rfl
  | succ count ih =>
      have h:=ih (parsePair input).suffix (parsePair input).first false
        (accepted && incomingPayloadCheck bound previous first (parsePair input))
      have parsed:=parsePair_length_bound input
      exact h.trans (by omega)

theorem scanIncoming_previous_le (bound : List Bool) (count : Nat) (input previous : List Bool) (first accepted : Bool) :
    (scanIncoming bound count input previous first accepted).previous.length≤ max previous.length input.length := by
  induction count generalizing input previous first accepted with
  | zero => exact Nat.le_max_left _ _
  | succ count ih =>
      have h:=ih (parsePair input).suffix (parsePair input).first false
        (accepted && incomingPayloadCheck bound previous first (parsePair input))
      have parsed:=parsePair_length_bound input
      exact h.trans (by omega)

theorem incomingPayloadCheck_frames (bound previous : List Bool) (first : Bool) (index count : Nat) (suffix : List Bool) :
    incomingPayloadCheck bound previous first
        (parsePair ((Encoding.product Encoding.natural Encoding.natural).encode (index,count)++suffix))=true ↔
      0<count ∧ index<Encoding.value bound ∧ ∀ p∈incomingPrevious previous first,p< index := by
  rw [show (Encoding.product Encoding.natural Encoding.natural).encode (index,count)=
    Encoding.frame index.bits++Encoding.frame count.bits from rfl]
  rw [parsePair_frames,incomingPayloadCheck_iff]
  simp only [Encoding.value_bits,true_and]
  cases first <;> simp [incomingPrevious]

theorem scanIncoming_sound (bound : List Bool) (count : Nat) (input previous : List Bool) (first accepted : Bool)
    (valid : (scanIncoming bound count input previous first accepted).accepted=true) :
    ∃ edges : List (Nat × Nat), edges.length=count ∧
      Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++
        (scanIncoming bound count input previous first accepted).suffix=input ∧
      incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges=true := by
  induction count generalizing input previous first accepted with
  | zero => exact ⟨[],rfl,rfl,rfl⟩
  | succ count ih =>
      let parsed:=parsePair input
      have flags:=scanIncoming_status bound count parsed.suffix parsed.first false
        (accepted && incomingPayloadCheck bound previous first parsed) valid
      have both : accepted=true ∧ incomingPayloadCheck bound previous first parsed=true := by
        simpa only [Bool.and_eq_true] using flags
      have item : incomingPayloadCheck bound previous first parsed=true := both.2
      obtain ⟨framed,indexCanonical,countCanonical,positive,inside,ordered⟩:=
        (incomingPayloadCheck_iff bound previous first parsed).mp item
      obtain ⟨edges,length,split,checks⟩:=ih parsed.suffix parsed.first false _ valid
      let edge:Nat×Nat:=⟨Encoding.value parsed.first,Encoding.value parsed.second⟩
      have pairSplit:=incoming_parsePair_accepted input framed
      have code:(Encoding.product Encoding.natural Encoding.natural).encode edge=
          Encoding.frame parsed.first++Encoding.frame parsed.second := by
        simp only [Encoding.product,Encoding.natural,edge,←indexCanonical,←countCanonical]
      refine ⟨edge::edges,by simp [length],?_,?_⟩
      · simp only [Encoding.sequence,List.append_assoc]
        rw [code,List.append_assoc]
        change Encoding.frame parsed.first++(Encoding.frame parsed.second++
          (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++
          (scanIncoming bound count parsed.suffix parsed.first false
            (accepted && incomingPayloadCheck bound previous first parsed)).suffix))=input
        rw [split]
        simpa only [List.append_assoc] using pairSplit
      · rw [incomingCheck_cons]
        refine ⟨positive,inside,?_,checks⟩
        cases first with
        | false => simpa [incomingPrevious,edge] using ordered
        | true => simp [incomingPrevious]

theorem scanIncoming_complete (bound previous : List Bool) (first : Bool)
    (edges : List (Nat × Nat)) (suffix : List Bool)
    (valid : incomingCheck (Encoding.value bound) (incomingPrevious previous first) edges=true) :
    (scanIncoming bound edges.length
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix) previous first true).accepted=true := by
  induction edges generalizing previous first with
  | nil => rfl
  | cons edge edges ih =>
      rcases edge with ⟨index,count⟩
      obtain ⟨positive,inside,ordered,tail⟩:=(incomingCheck_cons _ _ _ _ _).mp valid
      have item:incomingPayloadCheck bound previous first
          (parsePair ((Encoding.product Encoding.natural Encoding.natural).encode (index,count)++
            (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix)))=true :=
        (incomingPayloadCheck_frames _ _ _ _ _ _).mpr ⟨positive,inside,ordered⟩
      have tail':incomingCheck (Encoding.value bound) (incomingPrevious index.bits false) edges=true := by
        simpa only [incomingPrevious,Bool.false_eq_true,↓reduceIte,Encoding.value_bits] using tail
      have rest:=ih index.bits false tail'
      simp only [Encoding.sequence,List.length_cons,scanIncoming,List.append_assoc,item,Bool.true_and]
      simpa only [Encoding.product,Encoding.natural,parsePair_frames] using rest

end Counting.StackMachine.EncodingPrograms
