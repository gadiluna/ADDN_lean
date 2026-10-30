import Counting.ExternalCoverNormalizeMembership
import Counting.StackRoutineMove

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def preservingScratch : List (Fin 48) := membershipScratch ++ [43,44]

/-- Search the serialized row table in register 39 for the exact binary row
in register 38. Preserve both inputs, the current source and all other live
registers; put only the answer in register 22. -/
def preservingMembership (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (move (extra+45) (w 0) (w 43) (w 44))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+45) (w 39) (w 0) (w 44)))
      (sequence (rowsMembership extra w) (move (extra+45) (w 43) (w 0) (w 44))))

theorem preservingMembership_executes (extra : Nat) (w : RowWorkspace extra)
    (rows : List MatchingVerification.RawClause) (store : Fin (extra+48) → List Bool)
    (accepted : Bool) (tail : List Bool)
    (table : store (w 39)=(Encoding.list MatchingVerification.clauseCodec).encode rows)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈preservingScratch,store (w i)=[]) :
    ∃ time ≤ 5000*((store (w 0)).length+(store (w 39)).length+(store (w 38)).length+1)^3,
      Executes (preservingMembership extra w) store time
        (Function.update store (w 22) [matchingRow (store (w 38)) rows]) := by
  let saved := Function.update (Function.update store (w 43) (store (w 0))) (w 0) []
  have saving : Executes (move (extra+45) (w 0) (w 43) (w 44)) store
      (6*(store (w 0)).length+4) saved := by
    simpa [saved,empty,preservingScratch,w.injective.eq_iff] using
      move_executes (extra+45) (w 0) (w 43) (w 44)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) store (empty 44 (by simp [preservingScratch]))
  let copied := Function.update saved (w 0) (store (w 39))
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+45) (w 39) (w 0) (w 44))) saved
      (5*(store (w 39)).length+2) copied := by
    simpa +instances [saved,copied,w.injective.eq_iff] using
      copy_executes (extra+45) (w 39) (w 0) (w 44)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        (by simp [w.injective.eq_iff]) saved
        (by simp [saved,w.injective.eq_iff,empty,preservingScratch])
  have copiedEmpty (i : Fin 48) (member : i∈membershipScratch) : copied (w i)=[] := by
    have n0 : i≠0 := by intro h;subst i;simp [membershipScratch] at member
    have n43 : i≠43 := by intro h;subst i;simp [membershipScratch] at member
    simp [copied,saved,w.injective.eq_iff,n0,n43,empty i (by simp [preservingScratch,member])]
  obtain ⟨scanTime,scanBound,scanning⟩ := rowsMembership_executes extra w rows copied accepted [] tail
    (by simp [copied,table]) (by simp [copied,saved,w.injective.eq_iff,status]) copiedEmpty
  let checked := Function.update (Function.update copied (w 0) []) (w 22)
    [matchingRow (store (w 38)) rows]
  have scanAs : Executes (rowsMembership extra w) copied scanTime checked := by
    simpa [checked,copied,saved,w.injective.eq_iff] using scanning
  have restoring := move_executes (extra+45) (w 43) (w 0) (w 44)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) checked
    (by simp [checked,copied,saved,w.injective.eq_iff,empty,preservingScratch])
  have savedWord : checked (w 43)=store (w 0) := by simp [checked,copied,saved,w.injective.eq_iff]
  rw [savedWord] at restoring
  have restored : Function.update (Function.update checked (w 0)
      (store (w 0)++checked (w 0))) (w 43) []=
      Function.update store (w 22) [matchingRow (store (w 38)) rows] := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [checked,w.injective.eq_iff]
    · by_cases e43 : r=w 43
      · subst r;simp [w.injective.eq_iff,empty,preservingScratch]
      · by_cases e22 : r=w 22
        · subst r;simp [checked,w.injective.eq_iff]
        · simp [checked,copied,saved,e0,e43,e22]
  rw [restored] at restoring
  refine ⟨(6*(store (w 0)).length+4)+1+((5*(store (w 39)).length+2)+1+
      (scanTime+1+(6*(store (w 0)).length+4))),?_,
    saving.sequence (copying.sequence (scanAs.sequence restoring))⟩
  have copiedSource : copied (w 0)=store (w 39) := by simp [copied]
  have copiedQuery : copied (w 38)=store (w 38) := by simp [copied,saved,w.injective.eq_iff]
  rw [copiedSource,copiedQuery] at scanBound
  let size := (store (w 0)).length+(store (w 39)).length+(store (w 38)).length+1
  have scanLimit : scanTime ≤ 2500*size^3 := scanBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size];omega) _))
  have sourceBound : (store (w 0)).length ≤ size := by dsimp [size];omega
  have tableBound : (store (w 39)).length ≤ size := by dsimp [size];omega
  have one : 1 ≤ size := by dsimp [size];omega
  have power : size ≤ size^3 := Nat.le_self_pow (by decide) _
  change _ ≤ 5000*size^3
  omega

end Counting.External.CoverNormalization
