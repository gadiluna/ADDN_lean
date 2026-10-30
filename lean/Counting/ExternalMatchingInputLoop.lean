import Counting.ExternalMatchingInputTriple
import Counting.ExternalMatchingInputValidity

namespace Counting.External.MatchingInputValidation
open StackMachine StackMachine.Routine SATVerification MatchingVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def rowRange (bits : List Bool) (row : RawClause) : Bool :=
  (clauseToRaw row).all (fun value=>decide (value < bits.length))

def rowsRange (bits : List Bool) (rows : List RawClause) : Bool := rows.all (rowRange bits)

def rowsGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  forEach (w 27) (tripleGuard extra w)

theorem rowsGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (rows : List RawClause) (bits suffix tail : List Bool) (limit : Nat)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=Encoding.sequence MatchingVerification.clauseCodec rows++suffix)
    (sourceBound : (store (w 0)).length ≤ limit) (universeInput : store (w 17)=bits)
    (counter : store (w 27)=List.replicate rows.length true)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈indexScratch,store (w i)=[]) :
    ∃ time ≤ rows.length*(1000*(limit+bits.length+1)^3+2)+1,
      Executes (rowsGuard extra w) store time
        (Function.update (Function.update (Function.update store (w 27) []) (w 0) suffix)
          (w 1) ((accepted && rowsRange bits rows)::tail)) := by
  induction rows generalizing store accepted with
  | nil =>
    have counterEmpty : store (w 27)=[]:=counter
    obtain ⟨ran,halted⟩:=repeat_empty (w 27) (tripleGuard extra w) store counterEmpty
    have final : Function.update (Function.update (Function.update store (w 27) []) (w 0) suffix)
        (w 1) ((accepted && rowsRange bits [])::tail)=store := by
      simp only [rowsRange,List.all_nil,Bool.and_true]
      rw [←counterEmpty,Function.update_eq_self,←show store (w 0)=suffix from source,
        Function.update_eq_self,←status,Function.update_eq_self]
    exact ⟨1,by simp,⟨⟨1,store⟩,ran,halted,final.symm⟩⟩
  | cons row rest ih =>
    rcases row with ⟨⟨⟩,a,b,c⟩
    let current : RawClause:=((),a,b,c)
    let remaining:=Encoding.sequence MatchingVerification.clauseCodec rest++suffix
    let count:=List.replicate rest.length true
    let consumed:=Function.update store (w 27) count
    have consumedSource : consumed (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++remaining := by
      simpa only [consumed,Function.update_of_ne (by simp [w.injective.eq_iff] : w 0≠w 27),
        Encoding.sequence,MatchingVerification.clause_encode,MatchingVerification.clauseToRaw,
        MatchingVerification.literalCodec,List.append_assoc,remaining] using source
    have consumedEmpty (i : Fin 32) (member : i∈indexScratch) : consumed (w i)=[] := by
      have different : i≠27:=by intro same;subst i;simp [indexScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=tripleGuard_executes extra w consumed a b c accepted
      remaining tail consumedSource (by simp [consumed,w.injective.eq_iff,status]) consumedEmpty
    have consumedUniverse : consumed (w 17)=bits:=by simp [consumed,w.injective.eq_iff,universeInput]
    rw [consumedUniverse] at bodyBound bodyStore
    let next:=Function.update (Function.update consumed (w 0) remaining)
      (w 1) ((accepted && rowRange bits current)::tail)
    have nextSource : next (w 0)=remaining:=by simp [next,w.injective.eq_iff]
    have nextBound : (next (w 0)).length ≤ limit := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound
      dsimp [remaining]
      simp only [List.length_append]
      omega
    have nextEmpty (i : Fin 32) (member : i∈indexScratch) : next (w i)=[] := by
      have n0 : i≠0:=by intro same;subst i;simp [indexScratch] at member
      have n1 : i≠1:=by intro same;subst i;simp [indexScratch] at member
      simpa [next,w.injective.eq_iff,n0,n1] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih next (accepted && rowRange bits current)
      nextSource nextBound (by simp [next,consumed,w.injective.eq_iff,universeInput])
      (by simp [next,consumed,w.injective.eq_iff,count]) (by simp [next]) nextEmpty
    have firstRun:=repeat_iteration (w 27) (tripleGuard extra w) store true count
      (by simpa only [List.length_cons,List.replicate_succ,count] using counter)
      bodyTime finishBody bodyRun bodyHalt
    change Machine.run (step (rowsGuard extra w).program) (bodyTime+2) ⟨0,store⟩=
      some ⟨0,finishBody.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 1000*(limit+bits.length+1)^3 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have shorter : (consumed (w 0)).length ≤ limit:=by simpa [consumed,w.injective.eq_iff] using sourceBound
      omega
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases n1 : r=w 1
      · subst r;simp [rowsRange,Bool.and_assoc,current]
      · by_cases n0 : r=w 0
        · subst r;simp [w.injective.eq_iff]
        · by_cases n27 : r=w 27
          · subst r;simp [w.injective.eq_iff]
          · simp [next,consumed,n0,n1,n27]

end Counting.External.MatchingInputValidation
