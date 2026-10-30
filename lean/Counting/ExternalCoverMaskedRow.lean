import Counting.ExternalCoverRowMembership
import Counting.ExternalCoverSelectRow

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def maskedRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (rowMembership extra w) (selectMembership extra w)

def maskedRowResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (indices : List Nat) (element : Nat) (selected : Bool) (suffix maskTail : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 32) maskTail) (w 35)
    (if selected && indices.contains element then true::store (w 35) else store (w 35))

theorem maskedRow_executes (extra : Nat) (w : RowWorkspace extra)
    (indices : List Nat) (element : Nat) (store : Fin (extra+48) → List Bool)
    (accepted selected : Bool) (suffix tail maskTail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode indices++suffix)
    (status : store (w 1)=accepted::tail) (query : store (w 38)=Encoding.natural.encode element)
    (mask : store (w 32)=selected::maskTail)
    (empty : ∀ i∈membershipScratch,store (w i)=[]) :
    ∃ time ≤ 2100*((store (w 0)).length+(store (w 38)).length+1)^3,
      Executes (maskedRow extra w) store time (maskedRowResult w store indices element selected suffix maskTail) := by
  obtain ⟨readTime,readBound,reading⟩ := rowMembership_executes extra w indices store accepted suffix tail source status empty
  let read := Function.update (Function.update store (w 0) suffix) (w 22) [indices.contains element]
  have readAs : Executes (rowMembership extra w) store readTime read := by
    simpa only [query,matchingIndex_natural] using reading
  have selecting := selectMembership_executes extra w read selected (indices.contains element) maskTail []
    (by simp [read,w.injective.eq_iff,mask]) (by simp [read])
  have final : selectMembershipResult w read selected (indices.contains element) maskTail []=
      maskedRowResult w store indices element selected suffix maskTail := by
    funext r
    by_cases e22 : r=w 22
    · subst r;simp [selectMembershipResult,maskedRowResult,w.injective.eq_iff,empty,membershipScratch]
    · by_cases e0 : r=w 0
      · subst r;simp [selectMembershipResult,maskedRowResult,read,w.injective.eq_iff]
      · simp [selectMembershipResult,maskedRowResult,read,Function.update_apply,e22,e0,w.injective.eq_iff]
  rw [final] at selecting
  refine ⟨readTime+1+(if selected && indices.contains element then 3 else 2),?_,readAs.sequence selecting⟩
  have positive := Nat.one_le_pow' 3 ((store (w 0)).length+(store (w 38)).length)
  split <;> omega

end Counting.External.CoverVerification
