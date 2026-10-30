import Counting.StackRealizabilityValidationGate
import Counting.StackRealizabilityBootstrap

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000

/-- Exact binary language of accepted compact realizability certificates.
Every noncanonical or malformed tuple is rejected. -/
def encodedVerifier (input : List Bool) : Bool :=
  match Encoding.verifierInput.decodeExact input with
  | none => false
  | some (vista,values,ell,order) => RealizabilityVerifier.verify vista values.toArray ell order

def recoveredCheck : Routine 98 := sequence inputRecover canonicalCheck

def inputGate : Routine 98 := branchRead 85 recoveredCheck (pushBit 1 false)

theorem inputGate_executes (input : List Bool) :
    ∃ time ≤ Complexity.polynomial (canonicalCoefficient+10) 25 input.length,
      ∃ result : Store 98,
        Executes inputGate (inputSyntaxStore input [(Encoding.verifierInput.decodeExact input).isSome]) time result ∧
        result 1=[encodedVerifier input] := by
  have one : 1 ≤ (input.length+1)^25 := Nat.one_le_pow _ _ (by omega)
  cases decoded : Encoding.verifierInput.decodeExact input with
  | none =>
    let start := inputSyntaxStore input [false]
    let finish := Function.update start 1 [false]
    have selected : Executes (if false then recoveredCheck else pushBit 1 false) start 1 finish := by
      change Executes (pushBit 1 false) start 1 finish
      have run := pushBit_executes (1:Fin 100) false start
      simpa only [start,finish,inputSyntaxStore,show (1:Fin 100)≠79 by decide,show (1:Fin 100)≠85 by decide,
        ite_false] using run
    have branch := branchRead_executes (85:Fin 100) recoveredCheck (pushBit 1 false) false [] start finish 1
      (by simp [start,inputSyntaxStore]) selected
    refine ⟨4,?_,finish,?_,?_⟩
    · unfold Complexity.polynomial;rw [Nat.add_mul];omega
    · simpa only [inputGate,start,decoded,Option.isSome_none] using branch
    · simp [finish,encodedVerifier,decoded]
  | some value =>
    obtain ⟨vista,values,ell,order⟩ := value
    have source := (Encoding.Codec.decodeExact_iff Encoding.verifierInput input (vista,values,ell,order)).mp decoded
    have recovery := inputRecover_executes input
    obtain ⟨time,bound,result,checking,answer⟩ := canonicalCheck_executes vista values ell order
    rw [source] at bound checking
    have selected : Executes (if true then recoveredCheck else pushBit 1 false)
        (inputSyntaxStore input [true]) (4*input.length+3+1+time) result := recovery.sequence checking
    have branch := branchRead_executes (85:Fin 100) recoveredCheck (pushBit 1 false) true []
      (inputSyntaxStore input [true]) result (4*input.length+3+1+time)
      (by simp [inputSyntaxStore]) selected
    refine ⟨4*input.length+3+1+time+3,?_,result,?_,?_⟩
    · have linear : input.length+1 ≤ (input.length+1)^25 := Nat.le_self_pow (by decide) _
      unfold Complexity.polynomial at bound ⊢
      rw [Nat.add_mul]
      omega
    · simpa only [inputGate,decoded,Option.isSome_some] using branch
    · simpa only [encodedVerifier,decoded] using answer

def totalVerifier : Routine 98 := sequence verifierBootstrap (sequence inputSyntax inputGate)
def verifierCoefficient : Nat := canonicalCoefficient+107000

/-- A total execution theorem on arbitrary words. Canonicality, DAG
validity and count dimensions are tested by the program itself, so no
mathematical validity premise is supplied by its caller. -/
theorem totalVerifier_executes (input : List Bool) :
    ∃ time ≤ Complexity.polynomial verifierCoefficient 25 input.length,
      ∃ result : Store 98,
        Executes totalVerifier (inputStore 98 input) time result ∧
        result 1=[encodedVerifier input] := by
  have bootstrap := verifierBootstrap_executes input
  obtain ⟨t0,b0,r0⟩ := inputSyntax_executes input
  obtain ⟨t1,b1,result,r1,answer⟩ := inputGate_executes input
  refine ⟨_,?_,result,bootstrap.sequence (r0.sequence r1),answer⟩
  have positive : 1 ≤ input.length+1 := by omega
  have fourth : (input.length+1)^4 ≤ (input.length+1)^25 := Nat.pow_le_pow_right positive (by decide)
  have limit := b0.trans (Nat.mul_le_mul_left 106000 fourth)
  have linear : input.length+1 ≤ (input.length+1)^25 := Nat.le_self_pow (by decide) _
  have one := Nat.one_le_pow 25 (input.length+1) positive
  unfold Complexity.polynomial at b1 ⊢
  change 9*input.length+6+1+(t0+1+t1) ≤ (canonicalCoefficient+107000)*(input.length+1)^25
  rw [Nat.add_mul] at b1 ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
