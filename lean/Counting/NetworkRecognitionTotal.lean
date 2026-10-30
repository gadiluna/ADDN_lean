import Counting.NetworkRecognitionTyped
import Counting.NetworkRecognitionSyntax
import Counting.StackReadBranch

namespace Counting.StackMachine.NetworkRecognition
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def validNetworkWord (input:List Bool) : Bool :=
  ((Encoding.networkInput.decodeExact input).map Encoding.networkValid).getD false

def semanticGate : Routine 24 := branchRead 1 semanticCheck (skip 24)

theorem semanticGate_executes (input:List Bool) :
    ∃time ≤ 70000000003*(input.length+1)^7, ∃result:Store 24,
      Executes semanticGate (syntaxStore input (Encoding.networkInput.decodeExact input).isSome) time result ∧
        result 1=[validNetworkWord input] := by
  have one:1≤(input.length+1)^7:=Nat.one_le_pow _ _ (by omega)
  cases decoded:Encoding.networkInput.decodeExact input with
  | none =>
    have selected:Executes (if false then semanticCheck else skip 24) (syntaxStore input false) 0
        (syntaxStore input false):=skip_executes _
    have branch:=branchRead_executes (1:Fin 26) semanticCheck (skip 24) false []
      (syntaxStore input false) (syntaxStore input false) 0 (by simp [syntaxStore]) selected
    refine ⟨3,by omega,syntaxStore input false,?_,?_⟩
    · simpa only [semanticGate,decoded,Option.isSome_none] using branch
    · simp [syntaxStore,validNetworkWord,decoded]
  | some network =>
    have encoded:Encoding.networkInput.encode network=input:=(Encoding.networkInput.decodeExact_iff input network).mp decoded
    obtain ⟨time,bound,run⟩:=semanticCheck_executes (syntaxStore input true) true []
      (by simp [syntaxStore]) (by intro r n1 n17;simp [syntaxStore,n1,n17]) network []
      (by simp [syntaxStore,encoded])
    have source:syntaxStore input true 17=input:=by simp [syntaxStore]
    rw [source] at bound
    let result:=semanticCheckStore (syntaxStore input true) true [] network []
    have selected:Executes (if true then semanticCheck else skip 24) (syntaxStore input true) time result:=run
    have branch:=branchRead_executes (1:Fin 26) semanticCheck (skip 24) true []
      (syntaxStore input true) result time (by simp [syntaxStore]) selected
    refine ⟨time+3,by omega,result,?_,?_⟩
    · simpa only [semanticGate,decoded,Option.isSome_some] using branch
    · simp [result,semanticCheckStore,validNetworkWord,decoded]

def totalNetworkCheck : Routine 24 := sequence syntaxCheck semanticGate
def totalNetworkCoefficient : Nat := syntaxCoefficient+70000000005
def totalNetworkExponent : Nat := max 7 syntaxExponent

/-- Every bit string is handled: malformed encodings and inadmissible
networks return false through actual physical guards. -/
theorem totalNetworkCheck_executes (input:List Bool) :
    ∃time ≤ Complexity.polynomial totalNetworkCoefficient totalNetworkExponent input.length,
      ∃result:Store 24, Executes totalNetworkCheck (inputStore 24 input) time result ∧
        result 1=[validNetworkWord input] := by
  obtain ⟨first,firstBound,firstRun⟩:=syntaxCheck_executes input
  obtain ⟨second,secondBound,result,secondRun,answer⟩:=semanticGate_executes input
  let B:=input.length+1
  have positive:1≤B:=by dsimp [B];omega
  have firstLimit:first ≤ syntaxCoefficient*B^totalNetworkExponent:=by
    apply firstBound.trans
    unfold Complexity.polynomial
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _))
  have secondLimit:second≤70000000003*B^totalNetworkExponent:=by
    apply secondBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _))
  have one:1≤B^totalNetworkExponent:=Nat.one_le_pow _ _ positive
  refine ⟨first+1+second,?_,result,firstRun.sequence secondRun,answer⟩
  change first+1+second≤(syntaxCoefficient+70000000005)*B^totalNetworkExponent
  rw [Nat.add_mul]
  omega

theorem totalNetworkCheck_computes : ComputesIn totalNetworkCheck.program
    (fun input=>[validNetworkWord input])
    (Complexity.polynomial totalNetworkCoefficient totalNetworkExponent) := by
  intro input
  obtain ⟨time,bound,result,run,answer⟩:=totalNetworkCheck_executes input
  obtain ⟨finish,ran,halted,output⟩:=run
  exact ⟨time,finish,bound,⟨ran,halted⟩,by simpa only [output] using answer⟩

def networkValidationMachine : Machine.Program := Compiler.compile totalNetworkCheck.program

theorem networkValidationMachine_computes : Complexity.ComputesCleanIn networkValidationMachine
    (fun input=>[validNetworkWord input])
    (Complexity.polynomial (20*(totalNetworkCoefficient+29)^2) (2*(totalNetworkExponent+1))) :=
  Compiler.computesCleanIn_polynomial _ _ totalNetworkCheck_computes

@[simp] theorem validNetworkWord_encoded (input:Simulation.Input) :
    validNetworkWord (Encoding.networkInput.encode input)=Encoding.networkValid input := by
  have decoded:Encoding.networkInput.decodeExact (Encoding.networkInput.encode input)=some input:=
    (Encoding.networkInput.decodeExact_iff _ _).mpr rfl
  simp [validNetworkWord,decoded]

theorem validNetworkWord_eq_decodeNetwork (input:List Bool) :
    validNetworkWord input=(Encoding.decodeNetwork? input).isSome := by
  cases decoded:Encoding.networkInput.decodeExact input with
  | none => simp [validNetworkWord,Encoding.decodeNetwork?,decoded]
  | some network =>
    cases valid:Encoding.networkValid network <;> simp [validNetworkWord,Encoding.decodeNetwork?,decoded,valid]

end Counting.StackMachine.NetworkRecognition
