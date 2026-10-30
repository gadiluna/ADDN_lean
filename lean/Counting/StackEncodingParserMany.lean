import Counting.StackEncodingParserProduct

namespace Counting.StackMachine.EncodingPrograms

def manyEffect (effect : List Bool → ParseEffect) : Nat → List Bool → ParseEffect
  | 0,input => ⟨input,[],true⟩
  | count+1,input => productEffect effect (manyEffect effect count) input

namespace VerifiedParser

variable {registers : Nat} {source status output : Fin (registers+2)}
  {α : Type} {codec : Encoding.Codec α}
  (parser : VerifiedParser registers source status output α codec)

theorem many_suffix_le (count : Nat) (input : List Bool) :
    (manyEffect parser.effect count input).suffix.length ≤ input.length := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih => exact (ih (parser.effect input).suffix).trans (parser.suffix_le input)

theorem many_code_le (count : Nat) (input : List Bool) :
    (manyEffect parser.effect count input).code.length ≤
      count*Complexity.polynomial parser.coefficient parser.exponent input.length := by
  induction count generalizing input with
  | zero => simp [manyEffect]
  | succ count ih =>
    have head := parser.code_le input
    have tail := ih (parser.effect input).suffix
    have polynomial : Complexity.polynomial parser.coefficient parser.exponent (parser.effect input).suffix.length ≤
        Complexity.polynomial parser.coefficient parser.exponent input.length := by
      unfold Complexity.polynomial
      gcongr
      exact parser.suffix_le input
    simp only [manyEffect,productEffect,List.length_append]
    nlinarith [Nat.mul_le_mul_left count polynomial]

theorem many_sound (count : Nat) (input : List Bool)
    (accepted : (manyEffect parser.effect count input).accepted=true) :
    ∃ values : List α, values.length=count ∧
      Encoding.sequence codec values++(manyEffect parser.effect count input).suffix=input ∧
      (manyEffect parser.effect count input).code=Encoding.sequence codec values := by
  induction count generalizing input with
  | zero => exact ⟨[],rfl,rfl,rfl⟩
  | succ count ih =>
    have both : (parser.effect input).accepted=true ∧
        (manyEffect parser.effect count (parser.effect input).suffix).accepted=true := by
      simpa only [manyEffect,productEffect,Bool.and_eq_true] using accepted
    obtain ⟨value,firstSplit,firstCode⟩:=parser.sound input both.1
    obtain ⟨values,length,restSplit,restCode⟩:=ih (parser.effect input).suffix both.2
    refine ⟨value::values,by simp [length],?_,?_⟩
    · simp only [Encoding.sequence,manyEffect,productEffect,List.append_assoc]
      rw [restSplit,firstSplit]
    · simp only [manyEffect,productEffect,firstCode,restCode,Encoding.sequence]

theorem many_roundtrip (values : List α) (suffix : List Bool) :
    manyEffect parser.effect values.length (Encoding.sequence codec values++suffix)=
      ⟨suffix,Encoding.sequence codec values,true⟩ := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.length_cons,Encoding.sequence,List.append_assoc,manyEffect,productEffect,
      parser.roundtrip,ih,Bool.true_and]

theorem sequence_count_le (positive : ∀ value,0<(codec.encode value).length) (values : List α) :
    values.length≤(Encoding.sequence codec values).length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have first:=positive value
    simp only [Encoding.sequence,List.length_cons,List.length_append]
    omega

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
