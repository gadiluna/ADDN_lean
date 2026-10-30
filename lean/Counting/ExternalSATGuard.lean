import Counting.ExternalSATGuardPrepare
import Counting.ExternalSATRaw
import Counting.StackEncodingBranch

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

def guardedRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (guardPrepare extra w)
    (branchRoutine (w 1) (sequence (pushBit (w 1) true) (rawRoutine extra w)) (pushBit (w 1) false))

def guardedCoefficient := guardCoefficient+6010

theorem guardedRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → i≠17 → store (w i)=[]) :
    ∃ time ≤ guardedCoefficient*((store (w 0)).length+(store (w 17)).length+1)^5,
      ∃ result, Executes (guardedRoutine extra w) store time result ∧
        result (w 1)=(accepted && check (store (w 0)) (store (w 17)))::tail := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := guardPrepare_executes extra w store accepted tail status empty
  let ready := Function.update store (w 1) ((accepted && rawParser.exactEffect (store (w 0)))::tail)
  let popped := Function.update ready (w 1) tail
  have source : popped (w 0)=store (w 0) := by simp [popped,ready,w.injective.eq_iff]
  have witness : popped (w 17)=store (w 17) := by simp [popped,ready,w.injective.eq_iff]
  let S := (store (w 0)).length+(store (w 17)).length+1
  have Spositive : 1≤S := by dsimp [S];omega
  have preparePower : ((store (w 0)).length+1)^4≤S^5 :=
    (Nat.pow_le_pow_left (by dsimp [S];omega) 4).trans (Nat.pow_le_pow_right Spositive (by decide))
  have prepareLarge : prepareTime≤guardCoefficient*S^5 := prepareBound.trans (Nat.mul_le_mul_left _ preparePower)
  by_cases valid : (accepted && rawParser.exactEffect (store (w 0)))=true
  · have components : accepted=true ∧ rawParser.exactEffect (store (w 0))=true := by simpa only [Bool.and_eq_true] using valid
    have parsed : (CNFEncoding.rawCodec.decodeExact (store (w 0))).isSome=true := by
      rw [←rawParser.exactEffect_decodeExact]
      exact components.2
    obtain ⟨raw,decoded⟩ := Option.isSome_iff_exists.mp parsed
    have encoded := (Encoding.Codec.decodeExact_iff _ _ raw).mp decoded
    let initialized := Function.update popped (w 1) (true::tail)
    have pushing : Executes (pushBit (w 1) true) popped 1 initialized := by
      simpa [initialized,popped] using pushBit_executes (w 1) true popped
    have scratch (i : Fin 32) (member : i∈rawScratch) : initialized (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [rawScratch,formulaScratch,clauseScratch] at member
      have b : i≠1 := by intro same;subst i;simp [rawScratch,formulaScratch,clauseScratch] at member
      have c : i≠17 := by intro same;subst i;simp [rawScratch,formulaScratch,clauseScratch] at member
      simpa [initialized,popped,ready,w.injective.eq_iff,b] using empty i a b c
    obtain ⟨rawTime,rawBound,rawRun⟩ := rawRoutine_executes extra w raw (store (w 17)) [] tail initialized true
      (by simpa [initialized,w.injective.eq_iff,source] using encoded.symm)
      (by simp [initialized,w.injective.eq_iff,witness]) (by simp [initialized]) scratch
    have yes := pushing.sequence rawRun
    have branch := branch_executes_true (w 1) (sequence (pushBit (w 1) true) (rawRoutine extra w))
      (pushBit (w 1) false) ready _ tail _ (by simp [ready,valid]) yes
    have combined := preparing.sequence branch
    refine ⟨prepareTime+1+(1+(1+1+rawTime)),?_,_,combined,?_⟩
    · have initializedSource : initialized (w 0)=store (w 0) := by simp [initialized,w.injective.eq_iff,source]
      rw [initializedSource] at rawBound
      change rawTime≤6000*S^5 at rawBound
      change _≤guardedCoefficient*S^5
      unfold guardedCoefficient
      nlinarith [show 1≤S^5 from Nat.one_le_pow _ _ Spositive]
    · simp [check,decoded,components.1]
  · have invalid : (accepted && rawParser.exactEffect (store (w 0)))=false := Bool.eq_false_iff.mpr valid
    have pushing : Executes (pushBit (w 1) false) popped 1
        (Function.update popped (w 1) (false::tail)) := by
      simpa [popped] using pushBit_executes (w 1) false popped
    have branch := branch_executes_false (w 1) (sequence (pushBit (w 1) true) (rawRoutine extra w))
      (pushBit (w 1) false) ready _ tail _ (by simp [ready,invalid]) pushing
    have combined := preparing.sequence branch
    refine ⟨prepareTime+1+(1+1),?_,_,combined,?_⟩
    · have spare : 3≤6010*S^5 := (by decide : 3≤6010).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 6010 (Nat.one_le_pow 5 S Spositive))
      change prepareTime+1+(1+1)≤guardedCoefficient*S^5
      rw [guardedCoefficient,Nat.add_mul]
      calc
        prepareTime+1+(1+1) = prepareTime+3 := by omega
        _ ≤ guardCoefficient*S^5+6010*S^5 := Nat.add_le_add prepareLarge spare
    · have failure : (accepted && check (store (w 0)) (store (w 17)))=false := by
        cases decoded : CNFEncoding.rawCodec.decodeExact (store (w 0)) with
        | none => simp [check,decoded]
        | some raw =>
          have exactTrue : rawParser.exactEffect (store (w 0))=true := by rw [rawParser.exactEffect_decodeExact,decoded];rfl
          have rejected : accepted=false := by simpa [exactTrue] using invalid
          simp [rejected]
      simp [failure]

end Counting.External.SATVerification
