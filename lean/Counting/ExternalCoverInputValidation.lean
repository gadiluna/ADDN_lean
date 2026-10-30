import Counting.ExternalCoverInputChecked
import Counting.StackEncodingParserGuard

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def routine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ParserGuard.guardPrepare MatchingVerification.rawParser extra w)
    (branchRoutine (w 1) (sequence (pushBit (w 1) true) (rawGuard extra w)) (pushBit (w 1) false))

def coefficient:=ParserGuard.guardCoefficient MatchingVerification.rawParser+300020

def measured (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (raw : MatchingVerification.Raw) : Fin (extra+32) → List Bool :=
  Function.update (Function.update (Function.update (Function.update store
    (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
    (w 0) []) (w 1) [rawStatus raw]

def result (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool) : Fin (extra+32) → List Bool :=
  match MatchingVerification.rawCodec.decodeExact (store (w 0)) with
  | none=>Function.update store (w 1) [false]
  | some raw=>measured extra w store raw

theorem result_flag (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool) :
    result extra w store (w 1)=[validInput (store (w 0))] := by
  cases decoded : MatchingVerification.rawCodec.decodeExact (store (w 0)) with
  | none => simp [result,validInput,decoded]
  | some raw => simp [result,validInput,decoded,measured]

theorem inputRaw_sizes (input : X3CEncoding.Input) :
    (inputRaw input).1.length=3*input.1 ∧ (inputRaw input).2.length=input.2.1 := by
  have rawEq:=toRaw_inputRaw input
  have first:=congrArg (fun raw : X3CEncoding.Raw=>raw.1.length) rawEq
  have second:=congrArg (fun raw : X3CEncoding.Raw=>raw.2.length) rawEq
  simpa [MatchingVerification.toRaw,X3CEncoding.toRaw] using And.intro first second

theorem result_canonical (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (input : X3CEncoding.Input) (source : store (w 0)=X3CEncoding.codec.encode input) :
    result extra w store=
      Function.update (Function.update (Function.update (Function.update store
        (w 17) (List.replicate (3*input.1) true)) (w 25) (List.replicate input.2.1 true))
        (w 0) []) (w 1) [true] := by
  have decoded : MatchingVerification.rawCodec.decodeExact (store (w 0))=some (inputRaw input) := by
    apply (MatchingVerification.rawCodec.decodeExact_iff _ _).mpr
    exact (inputRaw_encode input).trans source.symm
  have valid : rawStatus (inputRaw input)=true := by
    apply (rawStatus_iff _).mpr
    rw [toRaw_inputRaw]
    exact X3CEncoding.toRaw_syntax input
  simp only [result,decoded,measured,valid,(inputRaw_sizes input).1,(inputRaw_sizes input).2]

/-- A total grammar and range validator. Accepted sources produce explicit
unary universe/edge counts; arbitrary binary coordinates are never expanded
beyond the explicit universe. All registers outside the workspace survive. -/
theorem routine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (status : store (w 1)=[true])
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ coefficient*((store (w 0)).length+1)^5,
      Executes (routine extra w) store time (result extra w store) := by
  obtain ⟨guardTime,guardBound,guardRun⟩:=ParserGuard.guardPrepare_executes
    MatchingVerification.rawParser MatchingVerification.rawParser_exponent_le_four extra w store true [] status
    (fun i n0 n1 _=>empty i n0 n1)
  let S:=(store (w 0)).length+1
  have positive : 1 ≤ S:=by dsimp [S];omega
  have power : S^4 ≤ S^5:=Nat.pow_le_pow_right positive (by decide)
  have guardLimit : guardTime ≤ ParserGuard.guardCoefficient MatchingVerification.rawParser*S^5:=
    guardBound.trans (Nat.mul_le_mul_left _ power)
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ positive
  cases decoded : MatchingVerification.rawCodec.decodeExact (store (w 0)) with
  | some raw =>
    have grammar : MatchingVerification.rawParser.exactEffect (store (w 0))=true := by
      rw [MatchingVerification.rawParser.exactEffect_decodeExact,decoded];rfl
    have unchanged : Function.update store (w 1) [(true && MatchingVerification.rawParser.exactEffect (store (w 0)))]=store := by
      rw [grammar];simp only [Bool.true_and,←status,Function.update_eq_self]
    rw [unchanged] at guardRun
    have encoded:=(MatchingVerification.rawCodec.decodeExact_iff _ raw).mp decoded
    let popped:=Function.update store (w 1) []
    have initialized : Function.update popped (w 1) [true]=store := by
      simp only [popped,Function.update_idem,←status,Function.update_eq_self]
    have pushing : Executes (pushBit (w 1) true) popped 1 store := by
      simpa only [popped,Function.update_self,initialized] using pushBit_executes (w 1) true popped
    have scratch (i : Fin 32) (member : i∈rawScratch) : store (w i)=[] := by
      have n0 : i≠0:=by intro same;subst i;simp [rawScratch,prefixScratch,tripleScratch,MatchingInputValidation.indexScratch] at member
      have n1 : i≠1:=by intro same;subst i;simp [rawScratch,prefixScratch,tripleScratch,MatchingInputValidation.indexScratch] at member
      exact empty i n0 n1
    obtain ⟨rawTime,rawBound,rawRun⟩:=rawGuard_executes extra w raw [] [] store true
      (by simpa only [List.append_nil] using encoded.symm) status scratch
    change Executes _ store rawTime (measured extra w store raw) at rawRun
    have branch:=branch_executes_true (w 1) (sequence (pushBit (w 1) true) (rawGuard extra w))
      (pushBit (w 1) false) store _ [] _ status (pushing.sequence rawRun)
    refine ⟨guardTime+1+(1+(1+1+rawTime)),?_,?_⟩
    · change rawTime ≤ 300010*S^5 at rawBound
      change _ ≤ coefficient*S^5
      unfold coefficient
      nlinarith only [guardLimit,rawBound,one]
    · simpa only [routine,result,decoded] using guardRun.sequence branch
  | none =>
    have grammar : MatchingVerification.rawParser.exactEffect (store (w 0))=false := by
      rw [MatchingVerification.rawParser.exactEffect_decodeExact,decoded];rfl
    let checked:=Function.update store (w 1) [false]
    have guardAs : Executes (ParserGuard.guardPrepare MatchingVerification.rawParser extra w) store guardTime checked := by
      simpa only [grammar,Bool.true_and] using guardRun
    let popped:=Function.update checked (w 1) []
    have restored : Function.update popped (w 1) [false]=checked := by simp only [popped,checked,Function.update_idem]
    have pushing : Executes (pushBit (w 1) false) popped 1 checked := by
      simpa only [popped,Function.update_self,restored] using pushBit_executes (w 1) false popped
    have branch:=branch_executes_false (w 1) (sequence (pushBit (w 1) true) (rawGuard extra w))
      (pushBit (w 1) false) checked checked [] 1 (by simp [checked]) pushing
    refine ⟨guardTime+1+(1+1),?_,?_⟩
    · change _ ≤ coefficient*S^5
      unfold coefficient
      nlinarith only [guardLimit,one]
    · simpa only [routine,result,decoded,checked] using guardAs.sequence branch

end Counting.External.CoverInputValidation
