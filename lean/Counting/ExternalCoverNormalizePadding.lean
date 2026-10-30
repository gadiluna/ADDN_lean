import Counting.ExternalCoverNormalizePaddingTriple

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def paddingRows (u : Nat) : List MatchingVerification.RawClause :=
  [consecutiveRow (u+3),consecutiveRow u]

def emitPadding (extra : Nat) (w : EmitWorkspace extra) : Routine (extra+4) :=
  sequence (prepend (w 0) [true,true,true])
    (sequence (paddingTriple extra w)
      (sequence (discard (w 0) 3) (paddingTriple extra w)))

/-- Emit the two forced triples in exactly the order of `pad.pad`, preserving
the original explicit-universe counter and all external state. -/
theorem emitPadding_executes (extra : Nat) (w : EmitWorkspace extra)
    (store : Fin (extra+6) → List Bool)
    (empty : ∀ i∈([2,3,4,5] : List (Fin 6)),store (w i)=[]) :
    ∃ time ≤ 250*((store (w 0)).length+6)^2,
      Executes (emitPadding extra w) store time
        (Function.update store (w 1)
          ((Encoding.sequence MatchingVerification.clauseCodec (paddingRows (store (w 0)).length)).reverse++store (w 1))) := by
  let u := (store (w 0)).length
  let lifted := Function.update store (w 0) ([true,true,true]++store (w 0))
  have lifting := prepend_executes (w 0) [true,true,true] store
  have liftedEmpty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) : lifted (w i)=[] := by
    have separate : i≠0 := by intro same;subst i;simp at member
    simp [lifted,w.injective.eq_iff,separate,empty i member]
  obtain ⟨t0,b0,r0⟩ := paddingTriple_executes extra w lifted liftedEmpty
  have liftedLength : (lifted (w 0)).length=u+3 := by
    simp only [lifted,Function.update_self,List.length_append,List.length_cons,List.length_nil]
    dsimp only [u]
    omega
  have liftedOutput : lifted (w 1)=store (w 1) := by simp [lifted,w.injective.eq_iff]
  let first := Function.update lifted (w 1)
    ((MatchingVerification.clauseCodec.encode (consecutiveRow (u+3))).reverse++store (w 1))
  have firstRun : Executes (paddingTriple extra w) lifted t0 first := by
    simpa only [first,liftedLength,liftedOutput] using r0
  have restoring := discard_executes (w 0) 3 first
  let restored := Function.update store (w 1)
    ((MatchingVerification.clauseCodec.encode (consecutiveRow (u+3))).reverse++store (w 1))
  have restoration : Function.update first (w 0) ((first (w 0)).drop 3)=restored := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [first,lifted,restored,w.injective.eq_iff]
    · simp [first,lifted,restored,e0,Function.update_apply]
  rw [restoration] at restoring
  have restoredEmpty (i : Fin 6) (member : i∈([2,3,4,5] : List (Fin 6))) : restored (w i)=[] := by
    have separate : i≠1 := by intro same;subst i;simp at member
    simp [restored,w.injective.eq_iff,separate,empty i member]
  obtain ⟨t1,b1,r1⟩ := paddingTriple_executes extra w restored restoredEmpty
  have final : Function.update restored (w 1)
      ((MatchingVerification.clauseCodec.encode (consecutiveRow (restored (w 0)).length)).reverse++restored (w 1))=
      Function.update store (w 1)
        ((Encoding.sequence MatchingVerification.clauseCodec (paddingRows u)).reverse++store (w 1)) := by
    simp [restored,w.injective.eq_iff,u,paddingRows,Encoding.sequence,List.reverse_append,List.append_assoc]
  rw [final] at r1
  have execution := lifting.sequence (firstRun.sequence (restoring.sequence r1))
  change Executes (emitPadding extra w) store (6+1+(t0+1+(6+1+t1))) _ at execution
  have limit0 : t0 ≤ 100*(u+6)^2 := by
    simpa only [liftedLength,Nat.add_assoc] using b0
  have limit1 : t1 ≤ 100*(u+3)^2 := by simpa [restored,w.injective.eq_iff,u] using b1
  refine ⟨_,?_,execution⟩
  change _ ≤ 250*(u+6)^2
  have p1 := Nat.pow_le_pow_left (show u+3 ≤ u+6 by omega) 2
  have square : 36 ≤ (u+6)^2 := by nlinarith only [Nat.zero_le u]
  omega

end Counting.External.CoverNormalization
