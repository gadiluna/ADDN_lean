import Counting.ExternalCoverMaskedRows
import Counting.ExternalCoverElementPrepare
import Counting.ExternalCoverMaskBounds

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def elementScratch : List (Fin 48) := membershipScratch++[0,23,32,35,38,40,41]

def elementAudit (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (prepareElement extra w)
    (sequence (maskedRows extra w)
      (sequence (checkCount extra w) (sequence (clear (w 38)) (pushBit (w 37) true))))

def elementAuditCost (stream count index : Nat) :=
  prepareElementCost stream count count index+1+
    (count*(2100*(stream+(Encoding.natural.encode index).length+1)^3+2)+1+1+
      (count+15+1+((Encoding.natural.encode index).length+1+1+1)))

theorem elementAudit_executes (extra : Nat) (w : RowWorkspace extra)
    (rows : List (List Nat)) (mask : List Bool) (element : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (tail : List Bool)
    (stream : store (w 34)=Encoding.sequence (Encoding.list Encoding.natural) rows)
    (witness : store (w 33)=mask) (count : store (w 25)=List.replicate rows.length true)
    (index : (store (w 37)).length=element) (sized : mask.length=rows.length)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈elementScratch,store (w i)=[]) :
    ∃ time ≤ elementAuditCost (store (w 34)).length rows.length element,
      Executes (elementAudit extra w) store time
        (Function.update (Function.update store (w 1) ((accepted && decide (hits rows mask element=1))::tail))
          (w 37) (true::store (w 37))) := by
  have prepEmpty (i : Fin 48) (member : i∈([0,18,20,23,29,32,38,41]:List (Fin 48))) : store (w i)=[] := by
    apply empty
    simp only [elementScratch,membershipScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    tauto
  obtain ⟨prepTime,prepBound,preparing⟩ := prepareElement_executes extra w store prepEmpty
  let prepared := prepareElementResult w store
  let query := Encoding.natural.encode element
  have preparedSource : prepared (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rows++[] := by
    simp [prepared,prepareElementResult,w.injective.eq_iff,stream]
  have preparedEmpty (i : Fin 48) (member : i∈membershipScratch) : prepared (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [membershipScratch] at member
    have b : i≠32 := by intro same;subst i;simp [membershipScratch] at member
    have c : i≠23 := by intro same;subst i;simp [membershipScratch] at member
    have d : i≠38 := by intro same;subst i;simp [membershipScratch] at member
    simpa [prepared,prepareElementResult,w.injective.eq_iff,a,b,c,d] using empty i (List.mem_append_left _ member)
  obtain ⟨loopTime,loopBound,looping⟩ := maskedRows_executes extra w rows element (store (w 34)).length mask prepared accepted [] tail []
    preparedSource (by simp [prepared,prepareElementResult,w.injective.eq_iff,count])
    (by simp [prepared,prepareElementResult,w.injective.eq_iff,status])
    (by simp [prepared,prepareElementResult,index])
    (by simp [prepared,prepareElementResult,w.injective.eq_iff,witness]) sized
    (by simp [prepared,prepareElementResult,w.injective.eq_iff]) preparedEmpty
  let counted := Function.update (Function.update store (w 38) query) (w 35) (List.replicate (hits rows mask element) true)
  have loopResult : maskedRowsResult w prepared rows mask element [] []=counted := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [maskedRowsResult,counted,w.injective.eq_iff,empty,elementScratch]
    · by_cases e23 : r=w 23
      · subst r;simp [maskedRowsResult,counted,w.injective.eq_iff,empty,elementScratch]
      · by_cases e32 : r=w 32
        · subst r;simp [maskedRowsResult,counted,w.injective.eq_iff,empty,elementScratch]
        · by_cases e35 : r=w 35
          · subst r;simp [maskedRowsResult,counted,prepared,prepareElementResult,w.injective.eq_iff,empty,elementScratch]
          · simp [maskedRowsResult,counted,prepared,prepareElementResult,query,index,Function.update_apply,e0,e23,e32,e35]
  rw [loopResult] at looping
  obtain ⟨checkTime,checkBound,checking⟩ := checkCount_executes extra w counted accepted tail
    (by simp [counted,w.injective.eq_iff,status]) (by simp [counted,w.injective.eq_iff,empty,elementScratch])
  let flag := (accepted && decide (hits rows mask element=1))::tail
  let checked := Function.update (Function.update store (w 38) query) (w 1) flag
  have checkResult : Function.update (Function.update counted (w 35) []) (w 1)
      ((accepted && decide (counted (w 35)=[true]))::tail)=checked := by
    simp only [counted,Function.update_self,singleton_counter]
    funext r
    by_cases e35 : r=w 35
    · subst r;simp [checked,w.injective.eq_iff,empty,elementScratch]
    · simp [checked,flag,Function.update_apply,e35]
  rw [checkResult] at checking
  have clearing := clear_executes (w 38) checked
  have queryStored : checked (w 38)=query := by simp [checked,w.injective.eq_iff]
  rw [queryStored] at clearing
  let cleaned := Function.update store (w 1) flag
  have clearResult : Function.update checked (w 38) []=cleaned := by
    funext r
    by_cases e38 : r=w 38
    · subst r;simp [cleaned,w.injective.eq_iff,empty,elementScratch]
    · simp [checked,cleaned,e38,Function.update_apply]
  rw [clearResult] at clearing
  have advancing := pushBit_executes (w 37) true cleaned
  have advanceAs : Executes (pushBit (w 37) true) cleaned 1
      (Function.update cleaned (w 37) (true::store (w 37))) := by
    simpa [cleaned,w.injective.eq_iff] using advancing
  have prepLimit : prepTime ≤ prepareElementCost (store (w 34)).length rows.length rows.length element := by
    simpa only [witness,count,List.length_replicate,sized,index] using prepBound
  have loopLimit : loopTime ≤ rows.length*(2100*((store (w 34)).length+query.length+1)^3+2)+1 := by
    simpa [prepared,prepareElementResult,query,index] using loopBound
  have checkLimit : checkTime ≤ rows.length+15 := by
    have hitBound := hits_le_rows rows mask element
    simp only [counted,Function.update_self,List.length_replicate] at checkBound
    omega
  refine ⟨prepTime+1+(loopTime+1+(checkTime+1+(query.length+1+1+1))),?_,
    preparing.sequence (looping.sequence (checking.sequence (clearing.sequence advanceAs)))⟩
  dsimp only [elementAuditCost]
  dsimp only [query] at loopLimit ⊢
  omega

end Counting.External.CoverVerification
