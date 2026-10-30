import Counting.ExternalCoverRowLayout
import Counting.ExternalCoverNormalizeRead
import Counting.StackComparePreserving

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine SATVerification CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def matchPositions : Fin 6 ↪ Fin 48 := ⟨![18,38,21,20,29,30],by decide⟩
def matchRoles (w : RowWorkspace extra) : Fin 6 ↪ Fin (extra+48) := matchPositions.trans w

def matchRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (readRow (extra+16) w.reader)
    (sequence (Compare.preservingEquality (extra+42) (matchRoles w)) (clear (w 18)))

def matchScratch : List (Fin 48) := [2,3,5,6,9,18,20,29,30]

theorem matchRow_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (row : MatchingVerification.RawClause) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=MatchingVerification.clauseCodec.encode row++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈matchScratch,store (w i)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 38)).length+1),
      Executes (matchRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 21)
          (decide (MatchingVerification.clauseCodec.encode row=store (w 38))::store (w 21))) := by
  obtain ⟨readTime,readBound,reading⟩ := readRow_executes (extra+16) w.reader store row accepted suffix tail source status
    (by
      intro i mem
      simp only [List.mem_cons,List.not_mem_nil] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|h
      all_goals first | contradiction | simpa [RowWorkspace.reader,rowReaderPositions] using empty _ (by decide))
  let code := MatchingVerification.clauseCodec.encode row
  let read := Function.update (Function.update store (w 0) suffix) (w 18) code
  have comparing := Compare.preservingEquality_executes (extra+42) (matchRoles w) read
    (by simp [matchRoles,matchPositions,read,w.injective.eq_iff,empty,matchScratch])
    (by simp [matchRoles,matchPositions,read,w.injective.eq_iff,empty,matchScratch])
    (by simp [matchRoles,matchPositions,read,w.injective.eq_iff,empty,matchScratch])
  let compared := Function.update read (w 21) (decide (code=store (w 38))::store (w 21))
  have compareAs : Executes (Compare.preservingEquality (extra+42) (matchRoles w)) read
      (Compare.preservingCost code (store (w 38))) compared := by
    simpa [matchRoles,matchPositions,read,compared,w.injective.eq_iff] using comparing
  have clearing := clear_executes (w 18) compared
  have header : compared (w 18)=code := by simp [compared,read,w.injective.eq_iff]
  rw [header] at clearing
  have final : Function.update compared (w 18) []=
      Function.update (Function.update store (w 0) suffix) (w 21) (decide (code=store (w 38))::store (w 21)) := by
    funext r
    by_cases e : r=w 18
    · subst r;simp [w.injective.eq_iff,empty,matchScratch]
    · simp [compared,read,e,Function.update_apply]
  rw [final] at clearing
  refine ⟨readTime+1+(Compare.preservingCost code (store (w 38))+1+(code.length+1)),?_,reading.sequence (compareAs.sequence clearing)⟩
  have comparedBound := Compare.preservingCost_le code (store (w 38))
  have codeBound : code.length≤(store (w 0)).length := by rw [source];dsimp [code];simp only [List.length_append];omega
  change readTime≤160*((store (w 0)).length+1) at readBound
  omega

end Counting.External.CoverNormalization
