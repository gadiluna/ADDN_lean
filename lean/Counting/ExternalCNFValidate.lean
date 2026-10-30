import Counting.ExternalCNFMeasureRaw
import Counting.ExternalSATGuardPrepare
import Counting.StackEncodingBranch

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

def validInput (input : List Bool) : Bool :=
  match CNFEncoding.rawCodec.decodeExact input with
  | none => false
  | some raw => validRaw raw

theorem validInput_iff (input : List Bool) : validInput input=true ↔
    ∃ formula : CNFInput,CNFEncoding.codec.encode formula=input := by
  constructor
  · intro valid
    cases decoded : CNFEncoding.rawCodec.decodeExact input with
    | none => simp [validInput,decoded] at valid
    | some raw =>
      have checked : validRaw raw=true := by simpa [validInput,decoded] using valid
      refine ⟨CNFEncoding.fromRaw raw,?_⟩
      change CNFEncoding.rawCodec.encode (CNFEncoding.toRaw (CNFEncoding.fromRaw raw))=input
      rw [validRaw_reencode raw checked]
      exact (Encoding.Codec.decodeExact_iff _ _ raw).mp decoded
  · rintro ⟨formula,encoded⟩
    have decoded : CNFEncoding.rawCodec.decodeExact input=some (CNFEncoding.toRaw formula) :=
      (Encoding.Codec.decodeExact_iff _ _ _).mpr encoded
    simp [validInput,decoded]

def validateRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (guardPrepare extra w)
    (branchRoutine (w 1) (sequence (pushBit (w 1) true) (measureRaw extra w)) (pushBit (w 1) false))

def validateCoefficient := guardCoefficient+230010

def Measures (extra : Nat) (w : SATWorkspace extra) (raw : CNFEncoding.Raw)
    (result : Fin (extra+32) → List Bool) : Prop :=
  result (w 17)=List.replicate raw.1.length true ∧
  result (w 25)=List.replicate raw.2.length true ∧
  result (w 31)=List.replicate (rawWidth raw.2) true

/-- Total canonical CNF syntax validation and exact input measurements. This
routine does not solve SAT: it checks only syntax, marker values and ranges. -/
theorem validateRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (status : store (w 1)=[true])
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ validateCoefficient*((store (w 0)).length+1)^5,
      ∃ result, Executes (validateRoutine extra w) store time result ∧
        result (w 1)=[validInput (store (w 0))] ∧
        ∀ raw,CNFEncoding.rawCodec.decodeExact (store (w 0))=some raw → Measures extra w raw result := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := guardPrepare_executes extra w store true [] status
    (fun i a b _ => empty i a b)
  let ready := Function.update store (w 1) [rawParser.exactEffect (store (w 0))]
  have preparingAs : Executes (guardPrepare extra w) store prepareTime ready := by simpa only [Bool.true_and] using preparing
  let popped := Function.update ready (w 1) []
  let initialized := Function.update popped (w 1) [true]
  have pushing : Executes (pushBit (w 1) true) popped 1 initialized := by
    simpa [initialized,popped] using pushBit_executes (w 1) true popped
  let S := (store (w 0)).length+1
  have Spositive : 1≤S := by dsimp [S];omega
  have powers : S^4≤S^5 := Nat.pow_le_pow_right Spositive (by decide)
  have prepareLarge : prepareTime≤guardCoefficient*S^5 := prepareBound.trans (Nat.mul_le_mul_left _ powers)
  cases decoded : CNFEncoding.rawCodec.decodeExact (store (w 0)) with
  | some raw =>
    have exactTrue : rawParser.exactEffect (store (w 0))=true := by rw [rawParser.exactEffect_decodeExact,decoded];rfl
    have encoded := (Encoding.Codec.decodeExact_iff _ _ raw).mp decoded
    have initializedSource : initialized (w 0)=store (w 0) := by simp [initialized,popped,ready,w.injective.eq_iff]
    have scratch (i : Fin 32) (member : i∈rawMeasureScratch) : initialized (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [rawMeasureScratch,measureScratch,formulaScratch,clauseScratch] at member
      have b : i≠1 := by intro same;subst i;simp [rawMeasureScratch,measureScratch,formulaScratch,clauseScratch] at member
      simpa [initialized,popped,ready,w.injective.eq_iff,b] using empty i a b
    obtain ⟨measureTime,measureBound,measuring⟩ := measureRaw_executes extra w raw [] [] initialized true
      (by simp [initializedSource,encoded]) (by simp [initialized]) scratch
    have yes := pushing.sequence measuring
    have branch := branch_executes_true (w 1) (sequence (pushBit (w 1) true) (measureRaw extra w))
      (pushBit (w 1) false) ready _ [] _ (by simp [ready,exactTrue]) yes
    have combined := preparingAs.sequence branch
    refine ⟨prepareTime+1+(1+(1+1+measureTime)),?_,_,combined,?_,?_⟩
    · rw [initializedSource] at measureBound
      change measureTime≤230000*S^5 at measureBound
      change _≤validateCoefficient*S^5
      unfold validateCoefficient
      nlinarith only [prepareLarge,measureBound,show 1≤S^5 from Nat.one_le_pow _ _ Spositive]
    · simp [validInput,decoded]
    · intro other otherDecoded
      have same : other=raw := Option.some.inj otherDecoded.symm
      subst other
      simp [Measures,w.injective.eq_iff]
  | none =>
    have exactFalse : rawParser.exactEffect (store (w 0))=false := by rw [rawParser.exactEffect_decodeExact,decoded];rfl
    have rejecting : Executes (pushBit (w 1) false) popped 1 (Function.update popped (w 1) [false]) := by
      simpa [popped] using pushBit_executes (w 1) false popped
    have branch := branch_executes_false (w 1) (sequence (pushBit (w 1) true) (measureRaw extra w))
      (pushBit (w 1) false) ready _ [] _ (by simp [ready,exactFalse]) rejecting
    have combined := preparingAs.sequence branch
    refine ⟨prepareTime+1+(1+1),?_,_,combined,?_,?_⟩
    · have spare : 3≤10*S^5 := (by omega : 3≤10).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 10 (Nat.one_le_pow 5 S Spositive))
      change _≤validateCoefficient*S^5
      calc
        prepareTime+1+(1+1)=prepareTime+3 := by omega
        _≤guardCoefficient*S^5+10*S^5 := Nat.add_le_add prepareLarge spare
        _=(guardCoefficient+10)*S^5 := (Nat.add_mul _ _ _).symm
        _≤validateCoefficient*S^5 := Nat.mul_le_mul_right _ (by unfold validateCoefficient;omega)
    · simp [validInput,decoded]
    · intro raw same;cases same

end Counting.External.CNFMachine
