import Counting.ExternalCoverUniverseLoop
import Counting.ExternalCoverVerifierPrepare
import Counting.ExternalCoverVerifierBounds

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem allHits_checkMask (input : X3CEncoding.Input) (mask : List Bool) (sized : mask.length=input.2.1) :
    allHits (X3CEncoding.toRaw input).2 mask 0 (3*input.1)=checkMask input mask := by
  apply Bool.eq_iff_iff.mpr
  rw [allHits_iff,checkMask_hits input mask sized]
  simp only [Nat.zero_add]
  exact ⟨fun h i=>h i.val i.isLt,fun h i bound=>h ⟨i,bound⟩⟩

def rawVerifier (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (verifierPrepare extra w) (universeLoop (extra+16) w.literal)

theorem rawVerifier_executes (extra : Nat) (w : VerifierWorkspace extra)
    (input : X3CEncoding.Input) (mask : List Bool) (store : Fin (extra+64) → List Bool)
    (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=X3CEncoding.codec.encode input)
    (status : store (w 1)=accepted::tail)
    (universeSize : store (w 17)=List.replicate (3*input.1) true)
    (count : store (w 25)=List.replicate input.2.1 true) (witness : store (w 33)=mask)
    (sized : mask.length=input.2.1)
    (empty : ∀ i : Fin 64,i≠0 → i≠1 → i≠17 → i≠25 → i≠33 → i≠51 → store (w i)=[]) :
    ∃ time ≤ 200000*((store (w 0)).length+1)^5,
      ∃ result,Executes (rawVerifier extra w) store time result ∧
        result (w 1)=(accepted && checkMask input mask)::tail := by
  let raw := X3CEncoding.toRaw input
  let stream := Encoding.sequence (Encoding.list Encoding.natural) raw.2
  have universeLength : raw.1.length=3*input.1 := by simp [raw,X3CEncoding.toRaw]
  have rowsLength : raw.2.length=input.2.1 := by simp [raw,X3CEncoding.toRaw]
  have prepEmpty (i : Fin 64) (member : i∈verifierPrepareScratch) : store (w i)=[] := by
    apply empty
    all_goals intro same;subst i;simp [verifierPrepareScratch,coverPrepareScratch] at member
  obtain ⟨prepTime,prepBound,preparing⟩ := verifierPrepare_executes extra w store raw accepted tail source status
    (by simp [universeSize,universeLength]) prepEmpty
  let prepared := verifierPrepareResult w store raw
  have loopEmpty (i : Fin 48) (member : i∈elementScratch) : prepared (w.literal i)=[] := by
    simp only [elementScratch,membershipScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    all_goals simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,empty]
  have loopStart : (prepared (w.literal 37)).length=0 := by
    simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,empty]
  obtain ⟨loopTime,loopBound,result,loopRun,loopHalt,loopResult⟩ := universeLoop_executes (extra+16) w.literal raw.2 mask
    (3*input.1) (3*input.1) prepared 0 accepted tail
    (by simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff])
    (by simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,witness])
    (by simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,count,rowsLength])
    loopStart (by simpa [rowsLength] using sized)
    (by simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,universeSize])
    (by omega) (by simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,status]) loopEmpty
  have loopAs : Executes (universeLoop (extra+16) w.literal) prepared loopTime result.store :=
    ⟨result,loopRun,loopHalt,rfl⟩
  refine ⟨prepTime+1+loopTime,?_,result.store,preparing.sequence loopAs,?_⟩
  · let length := (store (w 0)).length
    have universeBound : 3*input.1 ≤ length := by dsimp [length];rw [source];exact (X3CEncoding.input_size_bounds input).1
    have rowsBound : input.2.1 ≤ length := by dsimp [length];rw [source];exact (X3CEncoding.input_size_bounds input).2
    have streamBound : stream.length ≤ length := by
      dsimp [length];rw [source]
      change stream.length ≤ ((Encoding.list Encoding.boolean).encode raw.1++
        (Encoding.natural.encode raw.2.length++stream)).length
      simp only [List.length_append];omega
    have actualStream : prepared (w.literal 34)=stream := by
      simp [prepared,verifierPrepareResult,GeneratorWorkspace.literal,literalPositions,w.injective.eq_iff,stream]
    rw [actualStream,rowsLength] at loopBound
    have elementLimit := elementAuditCost_polynomial stream.length input.2.1 (3*input.1) length streamBound rowsBound universeBound
    have loopLimit : loopTime ≤ length*(100000*(length+1)^4+2)+1 := by
      apply loopBound.trans
      gcongr
    rw [universeLength] at prepBound
    have cube : ((store (w 0)).length+3*input.1+1)^3 ≤ 8*(length+1)^3 := by
      calc
        _ ≤ (2*(length+1))^3 := Nat.pow_le_pow_left (by dsimp [length] at *;omega) _
        _ = _ := by ring
    have prepLimit : prepTime ≤ 32800*(length+1)^3 := by
      have bound := prepBound.trans (Nat.mul_le_mul_left 4100 cube)
      nlinarith only [bound]
    have positive : 1 ≤ length+1 := by omega
    have third : (length+1)^3 ≤ (length+1)^5 := Nat.pow_le_pow_right positive (by decide)
    have linear : length+1 ≤ (length+1)^5 := Nat.le_self_pow (by decide) _
    have power : (length+1)^5=(length+1)^4*(length+1) := pow_succ _ _
    change prepTime+1+loopTime ≤ 200000*(length+1)^5
    nlinarith
  · rw [loopResult]
    have one : w 1=w.literal 1 := rfl
    rw [one]
    simp only [universeResult,Function.update_self,raw,allHits_checkMask input mask sized]

end Counting.External.CoverVerification
