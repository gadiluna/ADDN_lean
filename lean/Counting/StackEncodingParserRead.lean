import Counting.StackEncodingParserSkip

/-! Indexed access to an unframed sequence of structured codec values. The
index is a unary word: its length is the number of complete values skipped.
The input and index are consumed. This operation checks canonicality of the
visited prefix, not a surrounding list's count header. -/
namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

def readEffect (effect : List Bool → ParseEffect) (count : Nat) : List Bool → ParseEffect :=
  productEffect (skipEffect effect count) effect

namespace VerifiedParser

variable {registers : Nat} {source status output : Fin (registers+2)}
  {α : Type} {codec : Encoding.Codec α}
  (parser : VerifiedParser registers source status output α codec)

def read (counter : Fin (registers+2)) : Routine registers :=
  sequence (parser.skip counter) parser.routine

theorem read_suffix_le (count : Nat) (input : List Bool) :
    (readEffect parser.effect count input).suffix.length ≤ input.length :=
  (parser.suffix_le _).trans (parser.many_suffix_le count input)

theorem read_code_le (count : Nat) (input : List Bool) :
    (readEffect parser.effect count input).code.length ≤
      Complexity.polynomial parser.coefficient parser.exponent input.length := by
  have bound:=parser.code_le (manyEffect parser.effect count input).suffix
  have suffixBound:=parser.many_suffix_le count input
  have polynomial : Complexity.polynomial parser.coefficient parser.exponent
      (manyEffect parser.effect count input).suffix.length ≤
      Complexity.polynomial parser.coefficient parser.exponent input.length := by
    unfold Complexity.polynomial
    gcongr
  exact bound.trans polynomial

theorem read_sound (count : Nat) (input : List Bool)
    (accepted : (readEffect parser.effect count input).accepted=true) :
    ∃ before : List α, ∃ value : α, before.length=count ∧
      Encoding.sequence codec before++codec.encode value++
        (readEffect parser.effect count input).suffix=input ∧
      (readEffect parser.effect count input).code=codec.encode value := by
  have both : (manyEffect parser.effect count input).accepted=true ∧
      (parser.effect (manyEffect parser.effect count input).suffix).accepted=true := by
    simpa only [readEffect,productEffect,skipEffect,Bool.and_eq_true] using accepted
  obtain ⟨before,length,splitBefore,_⟩:=parser.many_sound count input both.1
  obtain ⟨value,splitValue,codeValue⟩:=parser.sound _ both.2
  refine ⟨before,value,length,?_,?_⟩
  · change (Encoding.sequence codec before++codec.encode value)++
      (parser.effect (manyEffect parser.effect count input).suffix).suffix=input
    rw [List.append_assoc,splitValue,splitBefore]
  · simpa only [readEffect,productEffect,skipEffect,List.nil_append] using codeValue

theorem read_roundtrip (before : List α) (value : α) (suffix : List Bool) :
    readEffect parser.effect before.length
      (Encoding.sequence codec before++codec.encode value++suffix)=
      ⟨suffix,codec.encode value,true⟩ := by
  rw [List.append_assoc]
  simp only [readEffect,productEffect,skipEffect,parser.many_roundtrip,parser.roundtrip,
    List.nil_append,Bool.true_and]

theorem read_accepts_iff (count : Nat) (input : List Bool) :
    (readEffect parser.effect count input).accepted=true ↔
      ∃ before : List α, ∃ value suffix, before.length=count ∧
        Encoding.sequence codec before++codec.encode value++suffix=input := by
  constructor
  · intro accepted
    obtain ⟨before,value,length,split,_⟩:=parser.read_sound count input accepted
    exact ⟨before,value,_,length,split⟩
  · rintro ⟨before,value,suffix,length,rfl⟩
    rw [←length,parser.read_roundtrip]

/-- In-range access to a typed sequence. This does not silently extend a
list's declared range into a trailing suffix. -/
theorem read_get (values : List α) (index : Fin values.length) (suffix : List Bool) :
    readEffect parser.effect index.val (Encoding.sequence codec values++suffix)=
      ⟨Encoding.sequence codec (values.drop (index.val+1))++suffix,
        codec.encode values[index],true⟩ := by
  have split : values=values.take index.val++values[index]::values.drop (index.val+1) := by
    have h:=List.take_append_drop index.val values
    rw [List.drop_eq_getElem_cons index.isLt] at h
    exact h.symm
  have takeLength : (values.take index.val).length=index.val := by
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt index.isLt)]
  have sequence_append (a b : List α) : Encoding.sequence codec (a++b)=
      Encoding.sequence codec a++Encoding.sequence codec b := by
    induction a with
    | nil => rfl
    | cons head a ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]
  conv_lhs => arg 3; arg 1; rw [split]
  rw [sequence_append]
  simp only [Encoding.sequence,List.append_assoc]
  have result:=parser.read_roundtrip (values.take index.val) values[index]
    (Encoding.sequence codec (values.drop (index.val+1))++suffix)
  simpa only [takeLength,List.append_assoc] using result

theorem read_executes (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    (counter : Fin (registers+2)) (cs : counter≠source) (ct : counter≠status) (co : counter≠output)
    (unused : counter∉parser.work) (bits : List Bool) (store : Store registers)
    (accepted : Bool) (tail : List Bool) (statusEq : store status=accepted::tail)
    (workEmpty : ∀ r∈parser.work,store r=[]) (outputEmpty : store output=[])
    (counterEq : store counter=bits) (limit : Nat) (inputBound : (store source).length ≤ limit) :
    ∃ time ≤ bits.length*(2*Complexity.polynomial parser.coefficient parser.exponent limit+2)+
        Complexity.polynomial parser.coefficient parser.exponent limit+4,
      Executes (parser.read counter) store time
        (parseStore source status output (Function.update store counter []) accepted tail
          (readEffect parser.effect bits.length (store source))) := by
  obtain ⟨skipTime,skipBound,skipRun⟩:=parser.skip_executes ss so statusOutput counter cs ct co unused
    bits store accepted tail statusEq workEmpty outputEmpty counterEq limit inputBound
  let middle:=parseStore source status output (Function.update store counter []) accepted tail
    (skipEffect parser.effect bits.length (store source))
  have nextStatus : middle status=
      (accepted && (skipEffect parser.effect bits.length (store source)).accepted)::tail := by
    simp [middle,parseStore,Ne.symm ss]
  have nextSource : middle source=(manyEffect parser.effect bits.length (store source)).suffix := by
    simp [middle,parseStore,skipEffect]
  have nextEmpty (r : Fin (registers+2)) (member : r∈parser.work) : middle r=[] := by
    obtain ⟨r0,r1,r2⟩:=parser.separate r member
    have rc : r≠counter := by intro h; subst r; exact unused member
    simpa only [middle,parseStore,if_neg r0,if_neg r1,if_neg r2,Function.update_of_ne rc] using
      workEmpty r member
  obtain ⟨readTime,readBound,readRun⟩:=parser.executes middle
    (accepted && (skipEffect parser.effect bits.length (store source)).accepted) tail nextStatus nextEmpty
  rw [nextSource] at readRun readBound
  have composed:=skipRun.sequence readRun
  change Executes _ _ _ (parseStore source status output
    (parseStore source status output (Function.update store counter []) accepted tail
      (skipEffect parser.effect bits.length (store source)))
    (accepted && (skipEffect parser.effect bits.length (store source)).accepted) tail
    (parser.effect (manyEffect parser.effect bits.length (store source)).suffix)) at composed
  rw [parseStore_product source status output ss so statusOutput] at composed
  refine ⟨skipTime+1+readTime,?_,composed⟩
  have restBound:=(parser.many_suffix_le bits.length (store source)).trans inputBound
  have polynomial : Complexity.polynomial parser.coefficient parser.exponent
      (manyEffect parser.effect bits.length (store source)).suffix.length ≤
      Complexity.polynomial parser.coefficient parser.exponent limit := by
    unfold Complexity.polynomial
    gcongr
  omega

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
