import Counting.ExternalMatchingInputIndex
import Counting.StackRoutineFixedPrefix

namespace Counting.External.MatchingInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def tripleGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (discard (w 0) (Encoding.natural.encode 3).length)
    (sequence (indexGuard extra w) (sequence (indexGuard extra w) (indexGuard extra w)))

theorem tripleGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (a b c : Nat) (accepted : Bool)
    (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈indexScratch,store (w i)=[]) :
    ∃ time ≤ 1000*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (tripleGuard extra w) store time
        (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && [a,b,c].all (fun value=>decide (value < (store (w 17)).length)))::tail)) := by
  let bits:=store (w 17)
  let afterA:=Encoding.natural.encode b++Encoding.natural.encode c++suffix
  let afterB:=Encoding.natural.encode c++suffix
  let rest:=Encoding.natural.encode a++afterA
  have sourceAs : store (w 0)=Encoding.natural.encode 3++rest := by
    simpa only [Encoding.list,Encoding.sequence,List.length_cons,List.length_nil,List.append_nil,List.append_assoc,rest,afterA] using source
  have discardRun:=discard_executes (w 0) (Encoding.natural.encode 3).length store
  simp only [sourceAs,List.drop_left] at discardRun
  let prepared:=Function.update store (w 0) rest
  have preparedEmpty (i : Fin 32) (member : i∈indexScratch) : prepared (w i)=[] := by
    have different : i≠0:=by intro same;subst i;simp [indexScratch] at member
    simpa [prepared,w.injective.eq_iff,different] using empty i member
  obtain ⟨ta,ba,ra⟩:=indexGuard_executes extra w prepared a accepted afterA tail
    (by simp [prepared,rest]) (by simp [prepared,w.injective.eq_iff,status]) preparedEmpty
  let first:=Function.update (Function.update prepared (w 0) afterA)
    (w 1) ((accepted && decide (a < bits.length))::tail)
  have bitsPrepared : prepared (w 17)=bits:=by simp [prepared,w.injective.eq_iff,bits]
  rw [bitsPrepared] at ra ba
  have firstEmpty (i : Fin 32) (member : i∈indexScratch) : first (w i)=[] := by
    have n0 : i≠0:=by intro same;subst i;simp [indexScratch] at member
    have n1 : i≠1:=by intro same;subst i;simp [indexScratch] at member
    simpa [first,w.injective.eq_iff,n0,n1] using preparedEmpty i member
  obtain ⟨tb,bb,rb⟩:=indexGuard_executes extra w first b (accepted && decide (a < bits.length)) afterB tail
    (by simp [first,w.injective.eq_iff,afterA,afterB,List.append_assoc]) (by simp [first]) firstEmpty
  have bitsFirst : first (w 17)=bits:=by simp [first,w.injective.eq_iff,bitsPrepared]
  rw [bitsFirst] at rb bb
  let second:=Function.update (Function.update first (w 0) afterB)
    (w 1) (((accepted && decide (a < bits.length)) && decide (b < bits.length))::tail)
  have secondEmpty (i : Fin 32) (member : i∈indexScratch) : second (w i)=[] := by
    have n0 : i≠0:=by intro same;subst i;simp [indexScratch] at member
    have n1 : i≠1:=by intro same;subst i;simp [indexScratch] at member
    simpa [second,w.injective.eq_iff,n0,n1] using firstEmpty i member
  obtain ⟨tc,bc,rc⟩:=indexGuard_executes extra w second c
    ((accepted && decide (a < bits.length)) && decide (b < bits.length)) suffix tail
    (by simp [second,w.injective.eq_iff,afterB]) (by simp [second]) secondEmpty
  have bitsSecond : second (w 17)=bits:=by simp [second,w.injective.eq_iff,bitsFirst]
  rw [bitsSecond] at rc bc
  have final : Function.update (Function.update second (w 0) suffix)
      (w 1) ((((accepted && decide (a < bits.length)) && decide (b < bits.length)) && decide (c < bits.length))::tail)=
      Function.update (Function.update store (w 0) suffix)
        (w 1) ((accepted && [a,b,c].all (fun value=>decide (value < bits.length)))::tail) := by
    funext r
    by_cases n1 : r=w 1
    · subst r;simp [Bool.and_assoc]
    · by_cases n0 : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · simp [second,first,prepared,n0,n1]
  rw [final] at rc
  have combined:=discardRun.sequence (ra.sequence (rb.sequence rc))
  refine ⟨2*(Encoding.natural.encode 3).length+1+(ta+1+(tb+1+tc)),?_,combined⟩
  let S:=(store (w 0)).length+bits.length+1
  have preparedSource : prepared (w 0)=rest:=by simp [prepared]
  have firstSource : first (w 0)=afterA:=by simp [first,w.injective.eq_iff]
  have secondSource : second (w 0)=afterB:=by simp [second,w.injective.eq_iff]
  rw [preparedSource] at ba
  rw [firstSource] at bb
  rw [secondSource] at bc
  have sizes : (Encoding.natural.encode 3).length ≤ (store (w 0)).length ∧
      rest.length ≤ (store (w 0)).length ∧ afterA.length ≤ (store (w 0)).length ∧ afterB.length ≤ (store (w 0)).length := by
    rw [sourceAs]
    simp only [List.length_append,rest,afterA,afterB]
    omega
  have aa : ta ≤ 200*S^3:=ba.trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by dsimp [S];omega) 3))
  have ab : tb ≤ 200*S^3:=bb.trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by dsimp [S];omega) 3))
  have ac : tc ≤ 200*S^3:=bc.trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by dsimp [S];omega) 3))
  have linear : S ≤ S^3:=Nat.le_self_pow (by decide) S
  change _ ≤ 1000*S^3
  dsimp [S] at linear aa ab ac ⊢
  omega

end Counting.External.MatchingInputValidation
