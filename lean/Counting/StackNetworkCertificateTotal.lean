import Counting.StackNetworkCertificateTyped
import Counting.StackRealizabilityVistaGuarded
import Counting.StackRealizabilitySyntaxCall

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 200000
set_option maxHeartbeats 2200000

def prepare : Routine 128 := sequence (ofProgram (ListPrograms.copyProgram 127 0 108 1))
  (sequence (clear 0) (pushBit 104 true))

theorem prepare_executes (input : List Bool) :
    Executes prepare (inputStore 128 input) (6*input.length+6)
      (file (initialData input true)) := by
  have copy := copy_executes 127 (0:Fin 130) 108 1 (by decide) (by decide) (by decide)
    (inputStore 128 input) (by simp [inputStore])
  rw [show inputStore 128 input 0=input by simp [inputStore],
    show inputStore 128 input 108=[] by simp [inputStore],List.append_nil] at copy
  let copied := Function.update (inputStore 128 input) 108 input
  have clear := clear_executes (0:Fin 130) copied
  rw [show copied 0=input by simp [copied,inputStore]] at clear
  let cleared := Function.update copied 0 []
  have flag := pushBit_executes (104:Fin 130) true cleared
  rw [show cleared 104=[] by simp [cleared,copied,inputStore]] at flag
  have final : Function.update cleared 104 [true]=file (initialData input true) := by
    funext r
    fin_cases r <;> simp [cleared,copied,inputStore,file,initialData]
  rw [final] at flag
  have run := copy.sequence (clear.sequence flag)
  simpa only [prepare,show 5*input.length+2+1+(input.length+1+1+1)=6*input.length+6 by omega] using run

def syntaxGuard : Routine 128 := VistaComplement.syntaxCall parser.recognition 8
def typedGate : Routine 128 := branchRead (context 4) typed (skip 128)
def guarded : Routine 128 := sequence syntaxGuard typedGate
def guardedCoefficient := 18*(parser.coefficient+20)+typedCoefficient+100

theorem guarded_executes (input : List Bool) :
    ∃ time ≤ Complexity.polynomial guardedCoefficient 27 input.length,
      ∃ result, Executes guarded (file (initialData input true)) time (file result) ∧
        result 4=[Counting.NetworkCertificate.predicate input] := by
  obtain ⟨t0,b0,r0⟩ := VistaComplement.syntaxCall_executes parser.recognition _ _ _ parser_computes
    (initialData input true) 8 true [] (by simp [initialData])
  have inputAt : initialData input true 8=input := by simp [initialData]
  rw [inputAt,Bool.true_and] at r0
  rw [inputAt] at b0
  have first : Function.update (initialData input true) 4
      [(Counting.NetworkCertificate.codec.decodeExact input).isSome]=
      initialData input (Counting.NetworkCertificate.codec.decodeExact input).isSome := by
    funext r
    by_cases r4:r=4 <;> simp [initialData,r4]
  rw [first] at r0
  have power := Nat.pow_le_pow_right (by omega : 1≤ input.length+1) parser_exponent
  have cost0 : t0≤18*(parser.coefficient+20)*(input.length+1)^27+23*input.length+65 := by
    have lifted := Nat.mul_le_mul_left (18*(parser.coefficient+20)) power
    unfold Complexity.polynomial at b0
    nlinarith only [b0,lifted]
  have linear : input.length+1≤(input.length+1)^27 := Nat.le_self_pow (by decide) _
  cases decoded : Counting.NetworkCertificate.codec.decodeExact input with
  | none =>
    have selected : Executes (if false then typed else skip 128) (file (initialData input false)) 0
        (file (initialData input false)) := skip_executes _
    have branch := branchRead_executes (context 4) typed (skip 128) false []
      (file (initialData input false)) (file (initialData input false)) 0 (by simp [initialData]) selected
    rw [decoded,Option.isSome_none] at r0
    refine ⟨t0+1+3,?_,initialData input false,r0.sequence branch,?_⟩
    · simp only [Complexity.polynomial,guardedCoefficient,Nat.add_mul];omega
    · simp [initialData,Counting.NetworkCertificate.predicate,decoded]
  | some value =>
    have encoded : Counting.NetworkCertificate.codec.encode value=input :=
      (Counting.NetworkCertificate.codec.decodeExact_iff _ _).mp decoded
    obtain ⟨t1,b1,result,r1,answer⟩ := typed_executes value
    rw [encoded] at b1 r1
    have selected : Executes (if true then typed else skip 128) (file (initialData input true)) t1
        (file result) := r1
    have branch := branchRead_executes (context 4) typed (skip 128) true []
      (file (initialData input true)) (file result) t1 (by simp [initialData]) selected
    rw [decoded,Option.isSome_some] at r0
    refine ⟨t0+1+(t1+3),?_,result,r0.sequence branch,?_⟩
    · simp only [Complexity.polynomial,guardedCoefficient,Nat.add_mul] at b1 ⊢;omega
    · simpa only [Counting.NetworkCertificate.predicate,decoded] using answer

def verifier : Routine 128 := sequence prepare (sequence guarded VistaComplement.finish)
def verifierCoefficient := guardedCoefficient+20

theorem verifier_executes (input : List Bool) :
    ∃ time ≤ Complexity.polynomial verifierCoefficient 27 input.length,
      ∃ result, Executes verifier (inputStore 128 input) time result ∧
        result 1=[Counting.NetworkCertificate.predicate input] := by
  have first := prepare_executes input
  obtain ⟨t1,b1,checked,r1,answer⟩ := guarded_executes input
  obtain ⟨result,r2,output⟩ := VistaComplement.finish_executes checked
    (Counting.NetworkCertificate.predicate input) answer
  have linear : input.length+1≤(input.length+1)^27 := Nat.le_self_pow (by decide) _
  refine ⟨6*input.length+6+1+(t1+1+3),?_,result,first.sequence (r1.sequence r2),output⟩
  simp only [Complexity.polynomial,verifierCoefficient,Nat.add_mul] at b1 ⊢
  omega

end Counting.StackMachine.NetworkCertificate
