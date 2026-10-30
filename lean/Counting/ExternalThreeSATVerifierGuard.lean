import Counting.ExternalThreeSATParser
import Counting.StackEncodingParserGuard
import Counting.ExternalSATGuard

namespace Counting.External.ThreeSATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def check (input witness : List Bool) : Bool := rawParser.exactEffect input && SATVerification.check input witness

def guardedRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ParserGuard.guardPrepare rawParser extra w) (SATVerification.guardedRoutine extra w)

def guardedCoefficient := ParserGuard.guardCoefficient rawParser+SATVerification.guardedCoefficient+2

theorem guardedRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → i≠17 → store (w i)=[]) :
    ∃ time ≤ guardedCoefficient*((store (w 0)).length+(store (w 17)).length+1)^5,
      ∃ result, Executes (guardedRoutine extra w) store time result ∧
        result (w 1)=(accepted && check (store (w 0)) (store (w 17)))::tail := by
  obtain ⟨guardTime,guardBound,guardRun⟩ := ParserGuard.guardPrepare_executes rawParser rawParser_exponent_le_four
    extra w store accepted tail status empty
  let guarded := Function.update store (w 1) ((accepted && rawParser.exactEffect (store (w 0)))::tail)
  have guardedEmpty (i : Fin 32) (a : i≠0) (b : i≠1) (c : i≠17) : guarded (w i)=[] := by
    simpa [guarded,w.injective.eq_iff,b] using empty i a b c
  obtain ⟨satTime,satBound,result,satRun,output⟩ := SATVerification.guardedRoutine_executes extra w guarded
    (accepted && rawParser.exactEffect (store (w 0))) tail (by simp [guarded]) guardedEmpty
  have source : guarded (w 0)=store (w 0) := by simp [guarded,w.injective.eq_iff]
  have witness : guarded (w 17)=store (w 17) := by simp [guarded,w.injective.eq_iff]
  rw [source,witness] at satBound output
  refine ⟨guardTime+1+satTime,?_,result,guardRun.sequence satRun,?_⟩
  · let S := (store (w 0)).length+(store (w 17)).length+1
    have positive : 1 ≤ S := by dsimp [S];omega
    have powers : ((store (w 0)).length+1)^4 ≤ S^5 :=
      (Nat.pow_le_pow_left (by dsimp [S];omega) 4).trans (Nat.pow_le_pow_right positive (by decide))
    have guardedBound := guardBound.trans (Nat.mul_le_mul_left (ParserGuard.guardCoefficient rawParser) powers)
    have one : 1 ≤ S^5 := Nat.one_le_pow _ _ positive
    change satTime ≤ SATVerification.guardedCoefficient*S^5 at satBound
    change _ ≤ guardedCoefficient*S^5
    dsimp only [guardedCoefficient]
    nlinarith only [guardedBound,satBound,one]
  · simpa only [check,Bool.and_assoc] using output

theorem exists_check_iff (input : List Bool) :
    input∈CNFMachine.ThreeSATLanguage ↔ ∃ bits,bits.length ≤ input.length ∧ check input bits=true := by
  constructor
  · rintro ⟨formula,encoded,three,satisfied⟩
    have sat : input∈CookLevin.SAT := ⟨formula,encoded,satisfied⟩
    obtain ⟨bits,bounded,accepted⟩ := (SATVerification.exists_check_iff input).mp sat
    refine ⟨bits,bounded,?_⟩
    have grammar : rawParser.exactEffect input=true := by
      rw [←encoded]
      exact (exactEffect_encoded formula).mpr three
    simp [check,grammar,accepted]
  · rintro ⟨bits,_bounded,accepted⟩
    have both : rawParser.exactEffect input=true ∧ SATVerification.check input bits=true := by
      simpa only [check,Bool.and_eq_true] using accepted
    obtain ⟨formula,encoded,_length,satisfied⟩ := (SATVerification.check_iff input bits).mp both.2
    have three : ∀ clause∈formula.2,clause.length=3 :=
      (exactEffect_encoded formula).mp (by simpa only [encoded] using both.1)
    exact ⟨formula,encoded,three,SATVerification.assignment bits,satisfied⟩

end Counting.External.ThreeSATVerification
