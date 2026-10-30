import Counting.ExternalCoverNormalizeEmit
import Counting.StackRoutineFixedPrefix

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def consecutiveRow (u : Nat) : MatchingVerification.RawClause := ((),u,u+1,u+2)

def paddingTriple (extra : Nat) (w : EmitWorkspace extra) : Routine (extra+4) :=
  sequence (prepend (w 1) (Encoding.natural.encode 3).reverse)
    (sequence (emitReversedNatural extra w)
      (sequence (pushBit (w 0) true)
        (sequence (emitReversedNatural extra w)
          (sequence (pushBit (w 0) true)
            (sequence (emitReversedNatural extra w) (discard (w 0) 2))))))

theorem paddingTriple_executes (extra : Nat) (w : EmitWorkspace extra)
    (store : Fin (extra+6) → List Bool)
    (empty : ∀ i∈([2,3,4,5] : List (Fin 6)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+3)^2,
      Executes (paddingTriple extra w) store time
        (Function.update store (w 1)
          ((MatchingVerification.clauseCodec.encode (consecutiveRow (store (w 0)).length)).reverse++store (w 1))) := by
  let u := (store (w 0)).length
  let header := Function.update store (w 1) ((Encoding.natural.encode 3).reverse++store (w 1))
  have headerRun := prepend_executes (w 1) (Encoding.natural.encode 3).reverse store
  have headerEmpty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) : header (w i)=[] := by
    have separate : i≠1 := by intro same;subst i;simp at member
    simp [header,w.injective.eq_iff,separate,empty i member]
  obtain ⟨t0,b0,r0⟩ := emitReversedNatural_executes extra w header headerEmpty
  let first := Function.update header (w 1) ((Encoding.natural.encode u).reverse++header (w 1))
  have firstRun : Executes (emitReversedNatural extra w) header t0 first := by
    simpa [first,header,w.injective.eq_iff,u] using r0
  have pushing0 := pushBit_executes (w 0) true first
  let up1 := Function.update first (w 0) (true::first (w 0))
  have up1Empty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) : up1 (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp at member
    have b : i≠1 := by intro same;subst i;simp at member
    simp [up1,first,header,w.injective.eq_iff,a,b,empty i member]
  obtain ⟨t1,b1,r1⟩ := emitReversedNatural_executes extra w up1 up1Empty
  let second := Function.update up1 (w 1) ((Encoding.natural.encode (u+1)).reverse++up1 (w 1))
  have secondRun : Executes (emitReversedNatural extra w) up1 t1 second := by
    simpa [second,up1,first,header,w.injective.eq_iff,u] using r1
  have pushing1 := pushBit_executes (w 0) true second
  let up2 := Function.update second (w 0) (true::second (w 0))
  have up2Empty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) : up2 (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp at member
    have b : i≠1 := by intro same;subst i;simp at member
    simp [up2,second,up1,first,header,w.injective.eq_iff,a,b,empty i member]
  obtain ⟨t2,b2,r2⟩ := emitReversedNatural_executes extra w up2 up2Empty
  let third := Function.update up2 (w 1) ((Encoding.natural.encode (u+2)).reverse++up2 (w 1))
  have thirdRun : Executes (emitReversedNatural extra w) up2 t2 third := by
    simpa [third,up2,second,up1,first,header,w.injective.eq_iff,u,Nat.add_assoc] using r2
  have restoring := discard_executes (w 0) 2 third
  have final : Function.update third (w 0) ((third (w 0)).drop 2)=
      Function.update store (w 1)
        ((MatchingVerification.clauseCodec.encode (consecutiveRow u)).reverse++store (w 1)) := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [third,up2,second,up1,first,header,w.injective.eq_iff]
    · by_cases e1 : r=w 1
      · subst r
        simp [third,up2,second,up1,first,header,w.injective.eq_iff,consecutiveRow,
          MatchingVerification.clause_encode,MatchingVerification.clauseToRaw,Encoding.list,
          MatchingVerification.literalCodec,Encoding.sequence,List.reverse_append,List.append_assoc]
      · simp [third,up2,second,up1,first,header,e0,e1]
  rw [final] at restoring
  have composed := headerRun.sequence (firstRun.sequence (pushing0.sequence
    (secondRun.sequence (pushing1.sequence (thirdRun.sequence restoring)))))
  change Executes (paddingTriple extra w) store (10+1+(t0+1+(1+1+(t1+1+(1+1+(t2+1+4)))))) _ at composed
  have limit0 : t0 ≤ 30*(u+1)^2 := by simpa [header,w.injective.eq_iff,u] using b0
  have limit1 : t1 ≤ 30*(u+2)^2 := by
    simpa [up1,first,header,w.injective.eq_iff,u,Nat.add_assoc] using b1
  have limit2 : t2 ≤ 30*(u+3)^2 := by
    simpa [up2,second,up1,first,header,w.injective.eq_iff,u,Nat.add_assoc] using b2
  refine ⟨_,?_,composed⟩
  change _ ≤ 100*(u+3)^2
  have p0 := Nat.pow_le_pow_left (show u+1 ≤ u+3 by omega) 2
  have p1 := Nat.pow_le_pow_left (show u+2 ≤ u+3 by omega) 2
  have square : 9 ≤ (u+3)^2 := by nlinarith only [Nat.zero_le u]
  omega

end Counting.External.CoverNormalization
