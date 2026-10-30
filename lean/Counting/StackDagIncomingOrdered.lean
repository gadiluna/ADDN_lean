import Counting.StackDagIncomingCanonical

/-! A reusable physical incoming-list checker with clean predecessor state.
Only the source suffix and accumulated status are changed. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def orderedIncomingPrefix (extra : Nat) (w : FullIncomingWorkspace extra) : Routine (extra+18):=
  sequence (pushBit (w 19) true)
    (sequence (incomingPrefix extra w) (sequence (clear (w 17)) (clear (w 19))))

def orderedIncomingStore (extra : Nat) (w : FullIncomingWorkspace extra) (store : Store (extra+18))
    (accepted : Bool) (tail : List Bool) (bound : Nat) (edges : List (Nat×Nat)) (suffix : List Bool) :=
  Function.update (Function.update store (w 0) suffix) (w 1) ((accepted && incomingCheck bound none edges)::tail)

theorem orderedIncomingPrefix_executes (extra : Nat) (w : FullIncomingWorkspace extra)
    (store : Store (extra+18)) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 20,2≤ i.val → i.val≤17 → store (w i)=[])
    (firstEmpty : store (w 19)=[]) (bound : Nat) (boundEq : store (w 18)=bound.bits)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix) :
    ∃ time ≤ 2520*((store (w 0)).length+bound.size+1)^3,
      Executes (orderedIncomingPrefix extra w) store time
        (orderedIncomingStore extra w store accepted tail bound edges suffix) := by
  have ne (i j : Fin 20) (different : i≠j) : w i≠w j:=fun eq=>different (w.injective eq)
  have initialized:=pushBit_executes (w 19) true store
  rw [firstEmpty] at initialized
  let ready:=Function.update store (w 19) [true]
  have readyEmpty (i : Fin 20) (lower : 2≤ i.val) (upper : i.val≤16) : ready (w i)=[] := by
    have different : i≠19:=by intro eq;subst i;norm_num at upper
    simp [ready,ne i 19 different,empty i lower (by omega)]
  obtain ⟨checkTime,checkBound,checkRun⟩:=incomingPrefix_executes extra w ready accepted true tail []
    (by simp [ready,ne 1 19 (by decide),status]) (by simp [ready]) readyEmpty
  let result:=incomingPrefixResult bound.bits (store (w 0)) [] true accepted
  let checked:=incomingScanStore (extra+10) (incomingBodyRoles extra w) ready tail [] result
  have checkResult : incomingScanStore (extra+10) (incomingBodyRoles extra w) ready tail []
      (incomingPrefixResult (ready (w 18)) (ready (w 0)) (ready (w 17)) true accepted)=checked := by
    simp [checked,result,ready,ne 18 19 (by decide),ne 0 19 (by decide),ne 17 19 (by decide),boundEq,empty]
  rw [checkResult] at checkRun
  have canonical : result.suffix=suffix ∧ result.accepted=(accepted && incomingCheck bound none edges):=by
    dsimp [result]
    rw [input]
    exact incomingPrefix_canonical bound accepted edges suffix
  have previousValue : checked (w 17)=result.previous:=by
    simp [checked,incomingScanStore,incomingBodyRoles,w.injective.eq_iff]
  have previousClear:=clear_executes (w 17) checked
  rw [previousValue] at previousClear
  let middle:=Function.update checked (w 17) []
  have firstValue : middle (w 19)=[result.first]:=by
    simp [middle,checked,incomingScanStore,incomingBodyRoles,w.injective.eq_iff]
  have firstClear:=clear_executes (w 19) middle
  rw [firstValue] at firstClear
  have final : Function.update middle (w 19) []=orderedIncomingStore extra w store accepted tail bound edges suffix:=by
    funext r
    by_cases r19 : r=w 19
    · subst r;simp [orderedIncomingStore,w.injective.eq_iff,firstEmpty]
    · by_cases r17 : r=w 17
      · subst r;simp [middle,orderedIncomingStore,w.injective.eq_iff,empty]
      · by_cases r0 : r=w 0 <;> by_cases r1 : r=w 1 <;>
          simp [middle,checked,incomingScanStore,incomingBodyRoles,ready,orderedIncomingStore,
            r19,r17,r0,r1,canonical.1,canonical.2]
  rw [final] at firstClear
  have previousBound : result.previous.length≤(store (w 0)).length:=by
    have raw:=scanIncoming_previous_le bound.bits (listCount (store (w 0))) (unframeSuffix (store (w 0))) [] true
      (accepted && listHeaderAccepted (store (w 0)))
    have suffixBound:=unframe_suffix_length (store (w 0))
    simpa only [result,incomingPrefixResult,List.length_nil,Nat.zero_max,Bool.true_and] using raw.trans suffixBound
  have checkedBound : checkTime≤2500*((store (w 0)).length+bound.size+1)^3:=by
    simpa [ready,ne 0 19 (by decide),ne 17 19 (by decide),ne 18 19 (by decide),empty,boundEq,
      Encoding.bits_length] using checkBound
  have linear:=Nat.le_self_pow (by decide : 3≠0) ((store (w 0)).length+bound.size+1)
  refine ⟨1+1+(checkTime+1+((result.previous.length+1)+1+([result.first].length+1))),?_,
    initialized.sequence (checkRun.sequence (previousClear.sequence firstClear))⟩
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.StackMachine.DagValidation
