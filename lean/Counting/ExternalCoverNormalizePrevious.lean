import Counting.ExternalCoverNormalizePreserving

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def previousScratch : List (Fin 48) := matchScratch ++ [22,24,43,44]

theorem rowSequence_append (before after : List MatchingVerification.RawClause) :
    Encoding.sequence MatchingVerification.clauseCodec (before++after)=
      Encoding.sequence MatchingVerification.clauseCodec before++
        Encoding.sequence MatchingVerification.clauseCodec after := by
  induction before with
  | nil => simp [Encoding.sequence]
  | cons head rest ih => simp only [List.cons_append,Encoding.sequence,List.append_assoc,ih]

/-- Search only the preceding rows. Register 39 holds the complete serialized
row sequence and register 40 counts the previous rows. The scan copies and
cleans the actual input; it does not receive a precomputed prefix for free. -/
def previousMembership (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (move (extra+45) (w 0) (w 43) (w 44))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 39) (w 0) (w 44)))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 40) (w 24) (w 44)))
        (sequence (pushBit (w 22) false)
          (sequence (matchPrefix extra w)
            (sequence (clear (w 0)) (move (extra+45) (w 43) (w 0) (w 44)))))))

theorem previousMembership_executes (extra : Nat) (w : RowWorkspace extra)
    (before after : List MatchingVerification.RawClause) (store : Fin (extra+48) → List Bool)
    (accepted : Bool) (tail : List Bool)
    (table : store (w 39)=Encoding.sequence MatchingVerification.clauseCodec (before++after))
    (counter : store (w 40)=List.replicate before.length true)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈previousScratch,store (w i)=[]) :
    ∃ time ≤ 1000*((store (w 0)).length+(store (w 39)).length+(store (w 38)).length+1)^2,
      Executes (previousMembership extra w) store time
        (Function.update store (w 22) [matchingRow (store (w 38)) before]) := by
  let saved := Function.update (Function.update store (w 43) (store (w 0))) (w 0) []
  have saving : Executes (move (extra+45) (w 0) (w 43) (w 44)) store
      (6*(store (w 0)).length+4) saved := by
    simpa [saved,empty,previousScratch,w.injective.eq_iff] using
      move_executes (extra+45) (w 0) (w 43) (w 44)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) store (empty 44 (by simp [previousScratch]))
  let copied := Function.update saved (w 0) (store (w 39))
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 39) (w 0) (w 44))) saved
      (5*(store (w 39)).length+2) copied := by
    simpa +instances [saved,copied,w.injective.eq_iff] using
      copy_executes (extra+45) (w 39) (w 0) (w 44)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) saved
        (by simp [saved,w.injective.eq_iff,empty,previousScratch])
  let counted := Function.update copied (w 24) (List.replicate before.length true)
  have counting : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 40) (w 24) (w 44))) copied
      (5*before.length+2) counted := by
    simpa +instances [copied,saved,counted,w.injective.eq_iff,counter,empty,previousScratch] using
      copy_executes (extra+45) (w 40) (w 24) (w 44)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) copied
        (by simp [copied,saved,w.injective.eq_iff,empty,previousScratch])
  let ready := Function.update counted (w 22) [false]
  have initializing : Executes (pushBit (w 22) false) counted 1 ready := by
    simpa [ready,counted,copied,saved,w.injective.eq_iff,empty,previousScratch] using
      pushBit_executes (w 22) false counted
  have readyEmpty (i : Fin 48) (member : i∈matchScratch) : ready (w i)=[] := by
    have n0 : i≠0 := by intro h;subst i;simp [matchScratch] at member
    have n22 : i≠22 := by intro h;subst i;simp [matchScratch] at member
    have n24 : i≠24 := by intro h;subst i;simp [matchScratch] at member
    have n43 : i≠43 := by intro h;subst i;simp [matchScratch] at member
    simp [ready,counted,copied,saved,w.injective.eq_iff,n0,n22,n24,n43,
      empty i (by simp [previousScratch,member])]
  have tableSplit : store (w 39)=Encoding.sequence MatchingVerification.clauseCodec before++
      Encoding.sequence MatchingVerification.clauseCodec after := by
    rw [table,rowSequence_append]
  obtain ⟨scanTime,scanBound,scanning⟩ := matchPrefix_executes extra w before (store (w 39)).length
    ready accepted false (Encoding.sequence MatchingVerification.clauseCodec after) tail []
    (by simp [ready,counted,copied,w.injective.eq_iff,tableSplit])
    (by simp [ready,counted,w.injective.eq_iff])
    (by simp [ready,counted,copied,saved,w.injective.eq_iff,status])
    (by simp [ready]) (by simp [ready,counted,copied,w.injective.eq_iff]) readyEmpty
  let checked := Function.update (Function.update (Function.update ready (w 0)
    (Encoding.sequence MatchingVerification.clauseCodec after)) (w 24) [])
    (w 22) [matchingRow (store (w 38)) before]
  have scanAs : Executes (matchPrefix extra w) ready scanTime checked := by
    simpa [matchPrefixResult,checked,ready,counted,copied,saved,w.injective.eq_iff] using scanning
  have clearing := clear_executes (w 0) checked
  have rest : checked (w 0)=Encoding.sequence MatchingVerification.clauseCodec after := by
    simp [checked,w.injective.eq_iff]
  rw [rest] at clearing
  let clean := Function.update checked (w 0) []
  have restoring := move_executes (extra+45) (w 43) (w 0) (w 44)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) clean
    (by simp [clean,checked,ready,counted,copied,saved,w.injective.eq_iff,empty,previousScratch])
  have savedWord : clean (w 43)=store (w 0) := by
    simp [clean,checked,ready,counted,copied,saved,w.injective.eq_iff]
  rw [savedWord] at restoring
  have restored : Function.update (Function.update clean (w 0)
      (store (w 0)++clean (w 0))) (w 43) []=
      Function.update store (w 22) [matchingRow (store (w 38)) before] := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [clean,w.injective.eq_iff]
    · by_cases e43 : r=w 43
      · subst r;simp [w.injective.eq_iff,empty,previousScratch]
      · by_cases e22 : r=w 22
        · subst r;simp [clean,checked,w.injective.eq_iff]
        · by_cases e24 : r=w 24
          · subst r;simp [clean,checked,w.injective.eq_iff,empty,previousScratch]
          · simp [clean,checked,ready,counted,copied,saved,e0,e43,e22,e24]
  rw [restored] at restoring
  refine ⟨(6*(store (w 0)).length+4)+1+((5*(store (w 39)).length+2)+1+
      ((5*before.length+2)+1+(1+1+(scanTime+1+
        ((Encoding.sequence MatchingVerification.clauseCodec after).length+1+1+(6*(store (w 0)).length+4)))))),?_,
    saving.sequence (copying.sequence (counting.sequence (initializing.sequence
      (scanAs.sequence (clearing.sequence restoring)))))⟩
  have readyQuery : ready (w 38)=store (w 38) := by
    simp [ready,counted,copied,saved,w.injective.eq_iff]
  rw [readyQuery] at scanBound
  have positive (row : MatchingVerification.RawClause) : 0 < (MatchingVerification.clauseCodec.encode row).length := by
    rw [MatchingVerification.clause_encode,Encoding.list_length];omega
  have countBound := EncodingPrograms.VerifiedParser.sequence_count_le positive before
  have lengthSplit := congrArg List.length tableSplit
  simp only [List.length_append] at lengthSplit
  let size := (store (w 0)).length+(store (w 39)).length+(store (w 38)).length+1
  have inputBound : (store (w 0)).length ≤ size := by dsimp [size];omega
  have tableBound : (store (w 39)).length ≤ size := by dsimp [size];omega
  have previousBound : before.length ≤ size := by omega
  have afterBound : (Encoding.sequence MatchingVerification.clauseCodec after).length ≤ size := by omega
  have scanLimit : scanTime ≤ size*(210*size+2)+1 := by
    apply scanBound.trans
    gcongr
    dsimp [size]
    omega
  have one : 1 ≤ size := by dsimp [size];omega
  have square : size ≤ size^2 := Nat.le_self_pow (by decide) _
  change _ ≤ 1000*size^2
  nlinarith only [scanLimit,inputBound,tableBound,previousBound,afterBound,one,square]

end Counting.External.CoverNormalization
