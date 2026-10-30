import Counting.ExternalCNFValidate

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

/-- Exact register state after successful parsing of a raw CNF encoding.
Semantic validity remains the returned flag; no assignment is searched. -/
theorem validateRoutine_canonical (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (raw : CNFEncoding.Raw)
    (source : store (w 0)=CNFEncoding.rawCodec.encode raw) (status : store (w 1)=[true])
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ validateCoefficient*((store (w 0)).length+1)^5,
      Executes (validateRoutine extra w) store time
        (Function.update (Function.update (Function.update (Function.update (Function.update store
          (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
          (w 31) (List.replicate (rawWidth raw.2) true)) (w 0) []) (w 1) [validRaw raw]) := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := guardPrepare_executes extra w store true [] status
    (fun i a b _=>empty i a b)
  have exactTrue : rawParser.exactEffect (store (w 0))=true := by
    rw [rawParser.exactEffect_decodeExact,source]
    rw [(Encoding.Codec.decodeExact_iff CNFEncoding.rawCodec _ raw).mpr rfl]
    rfl
  have unchanged : Function.update store (w 1) [(true && rawParser.exactEffect (store (w 0)))]=store := by
    rw [exactTrue];simp only [Bool.true_and,←status,Function.update_eq_self]
  rw [unchanged] at preparing
  let popped := Function.update store (w 1) []
  have initialized : Function.update popped (w 1) [true]=store := by
    simp only [popped,Function.update_idem,←status,Function.update_eq_self]
  have pushing : Executes (pushBit (w 1) true) popped 1 store := by
    have run := pushBit_executes (w 1) true popped
    simpa only [popped,Function.update_self,initialized] using run
  have scratch (i : Fin 32) (member : i∈rawMeasureScratch) : store (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [rawMeasureScratch,measureScratch,formulaScratch,clauseScratch] at member
    have b : i≠1 := by intro same;subst i;simp [rawMeasureScratch,measureScratch,formulaScratch,clauseScratch] at member
    exact empty i a b
  obtain ⟨measureTime,measureBound,measuring⟩ := measureRaw_executes extra w raw [] [] store true
    (by simpa using source) status scratch
  have yes := pushing.sequence measuring
  have branch := branch_executes_true (w 1) (sequence (pushBit (w 1) true) (measureRaw extra w)) (pushBit (w 1) false)
    store _ [] _ status yes
  have combined := preparing.sequence branch
  refine ⟨prepareTime+1+(1+(1+1+measureTime)),?_,?_⟩
  · let S := (store (w 0)).length+1
    have positive : 1≤S := by dsimp [S];omega
    have powers : S^4≤S^5 := Nat.pow_le_pow_right positive (by decide)
    have prepareLarge : prepareTime≤guardCoefficient*S^5 := prepareBound.trans (Nat.mul_le_mul_left _ powers)
    change measureTime≤230000*S^5 at measureBound
    change _≤validateCoefficient*S^5
    unfold validateCoefficient
    nlinarith only [prepareLarge,measureBound,show 1≤S^5 from Nat.one_le_pow _ _ positive]
  · simpa only [validateRoutine,Bool.true_and] using combined

end Counting.External.CNFMachine
