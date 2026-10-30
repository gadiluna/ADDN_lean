import Counting.ExternalCNFValidateExact
import Counting.ExternalThreeSATParser
import Counting.StackEncodingParserGuard

namespace Counting.External.MatchingValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

/-- Syntactic three-SAT, including explicit universe markers and index bounds.
No satisfying assignment is sought by this predicate. -/
def check (input : List Bool) : Bool :=
  ThreeSATVerification.rawParser.exactEffect input && CNFMachine.validInput input

theorem check_iff (input : List Bool) :
    check input = true ↔ ∃ formula : CNFInput,
      CNFEncoding.codec.encode formula = input ∧ ∀ clause ∈ formula.2, clause.length=3 := by
  simp only [check,Bool.and_eq_true]
  constructor
  · rintro ⟨grammar,valid⟩
    obtain ⟨formula,encoded⟩ := (CNFMachine.validInput_iff input).mp valid
    exact ⟨formula,encoded,(ThreeSATVerification.exactEffect_encoded formula).mp (by simpa only [encoded] using grammar)⟩
  · rintro ⟨formula,encoded,three⟩
    exact ⟨by simpa only [encoded] using (ThreeSATVerification.exactEffect_encoded formula).mpr three,
      (CNFMachine.validInput_iff input).mpr ⟨formula,encoded⟩⟩

def routine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ParserGuard.guardPrepare ThreeSATVerification.rawParser extra w)
    (branchRoutine (w 1)
      (sequence (pushBit (w 1) true) (CNFMachine.validateRoutine extra w))
      (pushBit (w 1) false))

def coefficient := ParserGuard.guardCoefficient ThreeSATVerification.rawParser + CNFMachine.validateCoefficient + 10

def measured (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (raw : CNFEncoding.Raw) : Fin (extra+32) → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
    (w 31) (List.replicate (CNFMachine.rawWidth raw.2) true)) (w 0) []) (w 1) [SATVerification.validRaw raw]

def result (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool) : Fin (extra+32) → List Bool :=
  if ThreeSATVerification.rawParser.exactEffect (store (w 0)) then
    match CNFEncoding.rawCodec.decodeExact (store (w 0)) with
    | some raw => measured extra w store raw
    | none => Function.update store (w 1) [false]
  else Function.update store (w 1) [false]

theorem result_flag (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool) :
    result extra w store (w 1) = [check (store (w 0))] := by
  unfold result check
  cases grammar : ThreeSATVerification.rawParser.exactEffect (store (w 0))
  · simp
  · cases decoded : CNFEncoding.rawCodec.decodeExact (store (w 0)) <;>
      simp [CNFMachine.validInput,measured,decoded]

theorem result_canonical (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (formula : CNFInput) (source : store (w 0)=CNFEncoding.codec.encode formula)
    (three : ∀ clause ∈ formula.2,clause.length=3) :
    result extra w store = measured extra w store (CNFEncoding.toRaw formula) := by
  have grammar : ThreeSATVerification.rawParser.exactEffect (store (w 0))=true := by
    rw [source]
    exact (ThreeSATVerification.exactEffect_encoded formula).mpr three
  have decoded : CNFEncoding.rawCodec.decodeExact (store (w 0))=some (CNFEncoding.toRaw formula) :=
    (CNFEncoding.rawCodec.decodeExact_iff _ _).mpr source.symm
  simp only [result,grammar,if_true,decoded]

/-- Total validation with a complete final-store contract. On a canonical
three-SAT source the explicit n, m and width counters are produced; external
registers, including the caller's saved input, are preserved. -/
theorem routine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (status : store (w 1)=[true])
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ coefficient*((store (w 0)).length+1)^5,
      Executes (routine extra w) store time (result extra w store) := by
  obtain ⟨guardTime,guardBound,guardRun⟩ := ParserGuard.guardPrepare_executes
    ThreeSATVerification.rawParser ThreeSATVerification.rawParser_exponent_le_four extra w store true [] status
    (fun i a b _ => empty i a b)
  let S := (store (w 0)).length+1
  have positive : 1 ≤ S := by dsimp [S];omega
  have power : S^4 ≤ S^5 := Nat.pow_le_pow_right positive (by decide)
  have guardLimit : guardTime ≤ ParserGuard.guardCoefficient ThreeSATVerification.rawParser*S^5 :=
    guardBound.trans (Nat.mul_le_mul_left _ power)
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ positive
  by_cases grammar : ThreeSATVerification.rawParser.exactEffect (store (w 0))=true
  · have unchanged : Function.update store (w 1) [(true && ThreeSATVerification.rawParser.exactEffect (store (w 0)))]=store := by
      rw [grammar];simp only [Bool.true_and,←status,Function.update_eq_self]
    rw [unchanged] at guardRun
    obtain ⟨raw,encoded,_three⟩ := (ThreeSATVerification.exactEffect_iff (store (w 0))).mp grammar
    have decoded : CNFEncoding.rawCodec.decodeExact (store (w 0))=some raw :=
      (CNFEncoding.rawCodec.decodeExact_iff _ raw).mpr encoded
    let popped := Function.update store (w 1) []
    have initialized : Function.update popped (w 1) [true]=store := by
      simp only [popped,Function.update_idem,←status,Function.update_eq_self]
    have pushing : Executes (pushBit (w 1) true) popped 1 store := by
      simpa only [popped,Function.update_self,initialized] using pushBit_executes (w 1) true popped
    obtain ⟨validateTime,validateBound,validation⟩ := CNFMachine.validateRoutine_canonical extra w store raw encoded.symm status empty
    change Executes _ store validateTime (measured extra w store raw) at validation
    have branch := branch_executes_true (w 1)
      (sequence (pushBit (w 1) true) (CNFMachine.validateRoutine extra w)) (pushBit (w 1) false)
      store _ [] _ status (pushing.sequence validation)
    refine ⟨guardTime+1+(1+(1+1+validateTime)),?_,?_⟩
    · change validateTime ≤ CNFMachine.validateCoefficient*S^5 at validateBound
      change _ ≤ coefficient*S^5
      unfold coefficient
      nlinarith only [guardLimit,validateBound,one]
    · simpa only [routine,result,grammar,if_true,decoded] using guardRun.sequence branch
  · have rejected : ThreeSATVerification.rawParser.exactEffect (store (w 0))=false := Bool.eq_false_iff.mpr grammar
    let checked := Function.update store (w 1) [false]
    have guardAs : Executes (ParserGuard.guardPrepare ThreeSATVerification.rawParser extra w) store guardTime checked := by
      simpa only [rejected,Bool.true_and] using guardRun
    let popped := Function.update checked (w 1) []
    have restored : Function.update popped (w 1) [false]=checked := by simp only [popped,checked,Function.update_idem]
    have pushing : Executes (pushBit (w 1) false) popped 1 checked := by
      simpa only [popped,Function.update_self,restored] using pushBit_executes (w 1) false popped
    have branch := branch_executes_false (w 1)
      (sequence (pushBit (w 1) true) (CNFMachine.validateRoutine extra w)) (pushBit (w 1) false)
      checked checked [] 1 (by simp [checked]) pushing
    refine ⟨guardTime+1+(1+1),?_,?_⟩
    · change _ ≤ coefficient*S^5
      unfold coefficient
      nlinarith only [guardLimit,one,Nat.zero_le CNFMachine.validateCoefficient]
    · simpa only [routine,result,rejected,Bool.false_eq_true,if_false,checked] using guardAs.sequence branch

end Counting.External.MatchingValidation
