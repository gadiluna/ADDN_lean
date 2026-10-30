import Counting.ExternalCoverNormalizeRetain

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def stepScratch : List (Fin 48) := previousScratch ++ [38]

def rowStep (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (readRow (extra+16) w.reader)
    (sequence (move (extra+45) (w 18) (w 38) (w 44))
      (sequence (previousMembership extra w) (retainRow extra w)))

def stepResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (row : MatchingVerification.RawClause) (before : List MatchingVerification.RawClause)
    (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) suffix)
    (w 36) (if row∈before then store (w 36)
      else (MatchingVerification.clauseCodec.encode row).reverse++store (w 36)))
    (w 41) (if row∈before then store (w 41) else true::store (w 41)))
    (w 40) (true::store (w 40))

theorem rowStep_executes (extra : Nat) (w : RowWorkspace extra)
    (row : MatchingVerification.RawClause) (before after : List MatchingVerification.RawClause)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (tail suffix : List Bool)
    (source : store (w 0)=MatchingVerification.clauseCodec.encode row++suffix)
    (table : store (w 39)=Encoding.sequence MatchingVerification.clauseCodec (before++row::after))
    (counter : store (w 40)=List.replicate before.length true)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈stepScratch,store (w i)=[]) :
    ∃ time ≤ 2000*((store (w 0)).length+(store (w 39)).length+1)^2,
      Executes (rowStep extra w) store time (stepResult w store row before suffix) := by
  have readEmpty (i : Fin 32) (member : i∈([2,3,5,6,9,18] : List (Fin 32))) : store (w.reader i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa [RowWorkspace.reader,rowReaderPositions] using empty _ (by simp [stepScratch,previousScratch,matchScratch])
  obtain ⟨readTime,readBound,reading⟩ := readRow_executes (extra+16) w.reader store row accepted suffix tail
    source status readEmpty
  let code := MatchingVerification.clauseCodec.encode row
  let read := Function.update (Function.update store (w 0) suffix) (w 18) code
  have readAs : Executes (readRow (extra+16) w.reader) store readTime read := reading
  have moving := move_executes (extra+45) (w 18) (w 38) (w 44)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) read
    (by simp [read,w.injective.eq_iff,empty,stepScratch,previousScratch])
  have readCode : read (w 18)=code := by simp [read]
  rw [readCode] at moving
  let ready := Function.update (Function.update store (w 0) suffix) (w 38) code
  have prepared : Function.update (Function.update read (w 38) (code++read (w 38))) (w 18) []=ready := by
    funext r
    by_cases e18 : r=w 18
    · subst r;simp [ready,w.injective.eq_iff,empty,stepScratch,previousScratch,matchScratch]
    · by_cases e38 : r=w 38
      · subst r;simp [ready,read,w.injective.eq_iff,empty,stepScratch]
      · simp [ready,read,e18,e38,Function.update_apply]
  rw [prepared] at moving
  have readyEmpty (i : Fin 48) (member : i∈previousScratch) : ready (w i)=[] := by
    have n0 : i≠0 := by intro h;subst i;simp [previousScratch,matchScratch] at member
    have n38 : i≠38 := by intro h;subst i;simp [previousScratch,matchScratch] at member
    simp [ready,w.injective.eq_iff,n0,n38,empty i (by simp [stepScratch,member])]
  obtain ⟨scanTime,scanBound,scanning⟩ := previousMembership_executes extra w before (row::after) ready accepted tail
    (by simp [ready,w.injective.eq_iff,table]) (by simp [ready,w.injective.eq_iff,counter])
    (by simp [ready,w.injective.eq_iff,status]) readyEmpty
  let seen := decide (row∈before)
  let checked := Function.update ready (w 22) [seen]
  have scanAs : Executes (previousMembership extra w) ready scanTime checked := by
    have queryEq : ready (w 38)=MatchingVerification.clauseCodec.encode row := by
      simp only [ready,Function.update_self,code]
    rw [queryEq,matchingRow_encoded] at scanning
    exact scanning
  obtain ⟨retainTime,retainBound,retaining⟩ := retainRow_executes extra w checked seen (by simp [checked])
  have final : retained w checked seen=stepResult w store row before suffix := by
    funext r
    by_cases e22 : r=w 22
    · subst r;simp [retained,stepResult,w.injective.eq_iff,empty,stepScratch,previousScratch]
    · by_cases e38 : r=w 38
      · subst r;simp [retained,stepResult,w.injective.eq_iff,empty,stepScratch]
      · simp [retained,stepResult,checked,ready,e22,e38,seen,code,Function.update_apply,w.injective.eq_iff]
  rw [final] at retaining
  refine ⟨readTime+1+(6*code.length+4+1+(scanTime+1+retainTime)),?_,
    readAs.sequence (moving.sequence (scanAs.sequence retaining))⟩
  have sourceSize : (store (w 0)).length=code.length+suffix.length := by
    rw [source,List.length_append]
  change readTime ≤ 160*((store (w 0)).length+1) at readBound
  have readySource : ready (w 0)=suffix := by simp [ready,w.injective.eq_iff]
  have readyTable : ready (w 39)=store (w 39) := by simp [ready,w.injective.eq_iff]
  have readyCode : ready (w 38)=code := by simp [ready]
  rw [readySource,readyTable,readyCode] at scanBound
  have checkedCode : checked (w 38)=code := by simp [checked,ready,w.injective.eq_iff]
  rw [checkedCode] at retainBound
  let size := (store (w 0)).length+(store (w 39)).length+1
  have scanLimit : scanTime ≤ 1000*size^2 := by
    apply scanBound.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [size]
    omega
  have inputBound : (store (w 0)).length+1 ≤ size := by dsimp [size];omega
  have codeBound : code.length ≤ size := by dsimp [size];omega
  have one : 1 ≤ size := by dsimp [size];omega
  have square : size ≤ size^2 := Nat.le_self_pow (by decide) _
  change _ ≤ 2000*size^2
  nlinarith only [readBound,retainBound,scanLimit,inputBound,codeBound,one,square]

end Counting.External.CoverNormalization
