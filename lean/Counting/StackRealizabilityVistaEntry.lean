import Counting.StackRealizabilityVistaGuarded
import Counting.StackEncodingFlaggedCorrectness

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def initialData (input witness : List Bool) (accepted : Bool) : Fin 30→List Bool :=
  fun i=>if i=4 then [accepted] else if i=8 then input else if i=9 then witness else []

def prepare : Routine 128 := sequence (ofProgram (flaggedProgram 126 0 108 1 104))
  (sequence (ofProgram (ListPrograms.copyProgram 127 0 109 1)) (clear 0))

theorem prepare_executes (input : List Bool) :
    ∃time≤9*input.length+9,
      Executes prepare (inputStore 128 input) time
        (file (initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome)) := by
  obtain ⟨t0,b0,r0⟩ := flagged_executes 126 (0:Fin 130) 108 1 104
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (inputStore 128 input) (by simp [inputStore])
  rw [flagged_result_updates 126 (0:Fin 130) 108 1 104
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (inputStore 128 input) (by simp [inputStore])] at r0
  simp only [inputStore,show (108:Fin 130)≠0 by decide,show (104:Fin 130)≠0 by decide,
    ↓reduceIte,List.append_nil] at r0
  let parsed := Function.update (Function.update (Function.update (inputStore 128 input)
    0 (unframeSuffix input)) 108 (unframePayload input)) 104 [(Encoding.unframe input).isSome]
  have copying := copy_executes 127 (0:Fin 130) 109 1 (by decide) (by decide) (by decide)
    parsed (by simp [parsed,inputStore])
  have p0 : parsed 0=unframeSuffix input := by simp [parsed]
  have p9 : parsed 109=[] := by simp [parsed,inputStore]
  rw [p0,p9,List.append_nil] at copying
  let copied := Function.update parsed 109 (unframeSuffix input)
  have clearing := clear_executes (0:Fin 130) copied
  have c0 : copied 0=unframeSuffix input := by simp [copied,p0]
  rw [c0] at clearing
  have final : Function.update copied 0 []=
      file (initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome) := by
    funext i
    fin_cases i <;> simp [copied,parsed,file,initialData,inputStore]

  rw [final] at clearing
  have suffixBound := unframe_suffix_length input
  refine ⟨t0+1+(5*(unframeSuffix input).length+2+1+((unframeSuffix input).length+1)),?_,
    r0.sequence (copying.sequence clearing)⟩
  change t0≤3*input.length+4 at b0
  omega

def predicate (input : List Bool) : Bool := (Encoding.unframe input).isSome &&
  Encoding.binaryComplementVerifier (unframePayload input) (unframeSuffix input)

def verifier : Routine 128 := sequence prepare (sequence guarded finish)
def verifierCoefficient : Nat := 2^25*guardedCoefficient+20

theorem verifier_executes (input : List Bool) :
    ∃time≤Complexity.polynomial verifierCoefficient 25 input.length,
      ∃result, Executes verifier (inputStore 128 input) time result ∧ result 1=[predicate input] := by
  obtain ⟨t0,b0,r0⟩ := prepare_executes input
  let ready := initialData (unframePayload input) (unframeSuffix input) (Encoding.unframe input).isSome
  obtain ⟨t1,b1,checked,r1,output⟩ := guarded_executes ready (Encoding.unframe input).isSome []
    (by simp [ready,initialData]) (by
      intro i hi
      rcases hi with h|h|h|h|h|h|h <;> subst i <;> simp [ready,initialData])
  have inputAt : ready 8=unframePayload input := by simp [ready,initialData]
  have witnessAt : ready 9=unframeSuffix input := by simp [ready,initialData]
  rw [inputAt,witnessAt] at b1 output
  obtain ⟨result,r2,resultAt⟩ := finish_executes checked (predicate input) output
  refine ⟨t0+1+(t1+1+3),?_,result,r0.sequence (r1.sequence r2),resultAt⟩
  have inBound := unframe_payload_length input
  have witnessBound := unframe_suffix_length input
  have power : ((unframePayload input).length+(unframeSuffix input).length+1)^25≤2^25*(input.length+1)^25 := by
    calc
      _≤(2*(input.length+1))^25 := Nat.pow_le_pow_left (by omega) 25
      _=_ := Nat.mul_pow _ _ _
  have checkBound := b1.trans (Nat.mul_le_mul_left guardedCoefficient power)
  have linear : input.length+1≤(input.length+1)^25 := Nat.le_self_pow (by decide) _
  change _≤(2^25*guardedCoefficient+20)*(input.length+1)^25
  simp only [Nat.add_mul,Nat.mul_assoc]
  change t1≤guardedCoefficient*(2^25*(input.length+1)^25) at checkBound
  have rearrange : guardedCoefficient*(2^25*(input.length+1)^25)=2^25*(guardedCoefficient*(input.length+1)^25) := by ring
  rw [rearrange] at checkBound
  omega

theorem predicate_pairWords (input witness : List Bool) :
    predicate (Encoding.pairWords input witness)=Encoding.binaryComplementVerifier input witness := by
  simp [predicate,Encoding.pairWords,unframePayload,unframeSuffix,Encoding.unframe_frame]

end Counting.StackMachine.VistaComplement
