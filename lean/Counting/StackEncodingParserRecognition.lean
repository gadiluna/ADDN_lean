import Counting.StackEncodingParser
import Counting.StackCompare
import Counting.StackRoutineBasic

namespace Counting.StackMachine.EncodingPrograms.VerifiedParser

set_option backward.isDefEq.respectTransparency false

variable {α : Type} {codec : Encoding.Codec α}

/-- Exact syntax recognition from a concrete prefix parser. The final
presence flag is combined with an actual empty-suffix comparison. -/
def recognition {extra : Nat} (parser : VerifiedParser (extra+2) 0 1 2 α codec) : Routine (extra+2) :=
  Routine.sequence (Routine.pushBit 1 true)
    (Routine.sequence parser.routine
      (Routine.sequence (Routine.ofProgram (Compare.equalityProgram (extra+2) 0 3 1))
        (Routine.ofProgram (combineFlagsProgram (extra+2) 1))))

def exactEffect {extra : Nat} (parser : VerifiedParser (extra+2) 0 1 2 α codec) (input : List Bool) : Bool :=
  (parser.effect input).accepted && decide ((parser.effect input).suffix=[])

theorem exactEffect_decodeExact {extra : Nat} (parser : VerifiedParser (extra+2) 0 1 2 α codec)
    (input : List Bool) : parser.exactEffect input=(codec.decodeExact input).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    have both : (parser.effect input).accepted=true ∧ (parser.effect input).suffix=[] := by
      simpa [exactEffect] using accepted
    obtain ⟨value,split,_⟩:=parser.sound input both.1
    have encoded : codec.encode value=input := by simpa only [both.2,List.append_nil] using split
    rw [(Encoding.Codec.decodeExact_iff _ input value).mpr encoded]
    rfl
  · intro accepted
    obtain ⟨value,decoded⟩:=Option.isSome_iff_exists.mp accepted
    have encoded:=(Encoding.Codec.decodeExact_iff _ input value).mp decoded
    have parsed : parser.effect input=⟨[],codec.encode value,true⟩ := by
      rw [←encoded]
      simpa only [List.append_nil] using parser.roundtrip value []
    simp [exactEffect,parsed]

/-- The bound covers every bit string. In particular, malformed input does
not rely on successful decoding to make the runtime proof applicable. -/
theorem recognition_computes {extra : Nat} (parser : VerifiedParser (extra+2) 0 1 2 α codec) :
    ComputesIn parser.recognition.program (fun input => [(codec.decodeExact input).isSome])
      (Complexity.polynomial (parser.coefficient+20) (max 1 parser.exponent)) := by
  intro input
  let start : Fin (extra+4) → List Bool := fun r => if r=0 then input else []
  let initialized := Function.update start 1 [true]
  have pushing := Routine.pushBit_executes (registers := extra+2) 1 true start
  have initSource : initialized 0=input := by simp [initialized,start]
  have initStatus : initialized 1=true::[] := by simp [initialized]
  have initWork (r : Fin (extra+4)) (member : r∈parser.work) : initialized r=[] := by
    obtain ⟨rs,rt,_⟩:=parser.separate r member
    simp [initialized,start,rs,rt]
  obtain ⟨parseTime,parseBound,parseRun⟩:=parser.executes initialized true [] initStatus initWork
  rw [initSource] at parseBound parseRun
  let parsed:=parseStore 0 1 2 initialized true [] (parser.effect input)
  have source : parsed 0=(parser.effect input).suffix := by simp [parsed,parseStore]
  have n30 : (3:Fin (extra+4))≠0 := by
    norm_num [Fin.ext_iff]
    rw [Nat.mod_eq_of_lt (by omega : 3<extra+4)]
    decide
  have n31 : (3:Fin (extra+4))≠1 := by
    norm_num [Fin.ext_iff]
    rw [Nat.mod_eq_of_lt (by omega : 3<extra+4)]
    decide
  have n32 : (3:Fin (extra+4))≠2 := by
    norm_num [Fin.ext_iff]
    rw [Nat.mod_eq_of_lt (by omega : 3<extra+4),Nat.mod_eq_of_lt (by omega : 2<extra+4)]
    decide
  have scratch : parsed 3=[] := by simp [parsed,parseStore,initialized,start,n30,n31,n32]
  have status : parsed 1=[(parser.effect input).accepted] := by simp [parsed,parseStore]
  have comparing:=Compare.equality_executes (extra+2) 0 3 1 (Ne.symm n30) (by norm_num [Fin.ext_iff]) n31 parsed
  rw [source,scratch,status] at comparing
  let compared:=Function.update (Function.update (Function.update parsed 0 []) 3 []) 1
    [decide ((parser.effect input).suffix=[]),(parser.effect input).accepted]
  have combining:=combineFlags_executes (extra+2) 1 compared (parser.effect input).accepted
    (decide ((parser.effect input).suffix=[])) [] (by simp [compared])
  have combined := pushing.sequence (parseRun.sequence (comparing.sequence combining))
  obtain ⟨finish,ran,halted,result⟩:=combined
  refine ⟨1+1+(parseTime+1+(Compare.equalityCost (parser.effect input).suffix []+1+3)),finish,?_,⟨ran,halted⟩,?_⟩
  · have suffixBound:=parser.suffix_le input
    have compareBound:=Compare.equalityCost_le (parser.effect input).suffix []
    simp only [List.length_nil,Nat.add_zero] at compareBound
    let E:=max 1 parser.exponent
    have powers : (input.length+1)^parser.exponent≤(input.length+1)^E := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have linear : input.length+1≤(input.length+1)^E := Nat.le_self_pow (by dsimp [E];omega) _
    unfold Complexity.polynomial at parseBound ⊢
    nlinarith [Nat.mul_le_mul_left parser.coefficient powers]
  · rw [result]
    change [parser.exactEffect input]=_
    rw [parser.exactEffect_decodeExact]

theorem recognition_computesCleanIn {extra : Nat} (parser : VerifiedParser (extra+2) 0 1 2 α codec) :
    Complexity.ComputesCleanIn (Compiler.compile parser.recognition.program)
      (fun input => [(codec.decodeExact input).isSome])
      (Complexity.polynomial (20*(parser.coefficient+extra+27)^2) (2*(max 1 parser.exponent+1))) := by
  have result:=Compiler.computesCleanIn_polynomial (parser.coefficient+20) (max 1 parser.exponent) parser.recognition_computes
  rw [show parser.coefficient+extra+27=parser.coefficient+20+(extra+2)+5 by omega]
  exact result

end Counting.StackMachine.EncodingPrograms.VerifiedParser
