import Counting.StackDagDistinctPrevious

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def distinctAtRoutine : Routine 33:=sequence (mapRegisters nodeAtReadRoles DagParser.preservingNodeRead)
  (sequence distinctPreviousRoutine (sequence (clear 28) (pushBit 29 true)))

def distinctAtStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (index : Fin values.length) : Store 33:=
  Function.update (Function.update store 1 ((accepted && distinctRange values values[index] 0 index.val)::tail))
    29 (true::store 29)

theorem distinctAt_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e28 : store 28=[])
    (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (budget : (store 29).length=index.val) :
    ∃ time ≤ 200000*((store 17).length+1)^5,
      Executes distinctAtRoutine store time (distinctAtStore store accepted tail values index) := by
  let localStore : Store 18:=store ∘ nodeAtReadRoles
  have localWork (r : Fin 17) (ne : r≠1) : localStore (DagParser.nodeRoles r)=[]:=by
    have small : r.val<18:=by have:=r.isLt;omega
    have rsmall : (nodeAtReadRoles (DagParser.nodeRoles r)).val<17:=by simp [nodeAtReadRoles,DagParser.nodeRoles,small]
    have rne : nodeAtReadRoles (DagParser.nodeRoles r)≠1:=by
      intro eq;apply ne;apply Fin.ext
      simpa [nodeAtReadRoles,small,DagParser.nodeRoles] using congrArg (fun r:Fin 35=>r.val) eq
    exact work _ rsmall rne
  obtain ⟨readTime,readBound,readRun⟩:=DagParser.preservingNodeRead_get localStore accepted tail
    (by simp [localStore,nodeAtReadRoles,status]) localWork
    (by simp [localStore,nodeAtReadRoles,e28]) values index suffix
    (by simp [localStore,nodeAtReadRoles,source]) (by simp [localStore,nodeAtReadRoles,budget])
  let selected:=Function.update store 28 (Encoding.node.encode values[index])
  have reading : Executes (mapRegisters nodeAtReadRoles DagParser.preservingNodeRead) store readTime selected:=by
    apply relocate_executes_frame DagParser.preservingNodeRead nodeAtReadRoles store selected localStore
      (Function.update localStore 19 (Encoding.node.encode values[index])) readTime rfl _ _ readRun
    · intro r;fin_cases r <;> simp [selected,localStore,nodeAtReadRoles]
    · intro r outside
      have n28 : r≠28:=by intro eq;subst r;exact outside 19 rfl
      simp [selected,n28]
  have selectedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : selected r=[]:=by
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [selected,n28,work r small ne]
  obtain ⟨checkTime,checkBound,checking⟩:=distinctPrevious_executes selected accepted tail
    (by simp [selected,status]) selectedWork (by simp [selected,e18]) (by simp [selected,e19])
    (by simp [selected,e20]) values index suffix (by simp [selected,source])
    (by simp [selected,budget]) (by simp [selected])
  let checked:=Function.update selected 1 ((accepted && distinctRange values values[index] 0 index.val)::tail)
  have clearing:=clear_executes (28:Fin 35) checked
  have checkedCode : checked 28=Encoding.node.encode values[index]:=by simp [checked,selected]
  rw [checkedCode] at clearing
  let cleaned:=Function.update checked 28 []
  have pushing:=pushBit_executes (29:Fin 35) true cleaned
  have final : Function.update cleaned 29 (true::cleaned 29)=distinctAtStore store accepted tail values index:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r28 : r=28 <;> by_cases r29 : r=29 <;>
      simp [distinctAtStore,cleaned,checked,selected,r1,r28,r29,e28]
  rw [final] at pushing
  have readSource : localStore 17=store 17:=by simp [localStore,nodeAtReadRoles]
  have readIndex : (localStore 18).length=index.val:=by simp [localStore,nodeAtReadRoles,budget]
  rw [readSource,readIndex] at readBound
  have checkSource : selected 17=store 17:=by simp [selected]
  rw [checkSource] at checkBound
  have count:=node_sequence_count_le values
  have member:=node_sequence_member_le values values[index] (List.getElem_mem index.isLt)
  have indexBound : index.val≤(store 17).length:=by rw [source,List.length_append];have:=index.isLt;omega
  have nodeLength : (Encoding.node.encode values[index]).length≤(store 17).length:=by rw [source,List.length_append];omega
  let S:=(store 17).length+1
  have spos : 1≤S:=by dsimp only [S];omega
  have factor : 2*index.val+3≤3*S:=by dsimp only [S];omega
  have readLimit : readTime≤6100*S^4+14:=by
    have leading : (2*index.val+3)*2029*((store 17).length+1)^3≤6087*S^4:=by
      calc
        _≤(3*S)*2029*S^3:=by gcongr
        _=6087*S^4:=by ring
    have linear : S≤S^4:=Nat.le_self_pow (by decide) _
    dsimp only [S] at leading linear ⊢
    omega
  have fourth : S^4≤S^5:=Nat.pow_le_pow_right spos (by decide)
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have one : 1≤S^5:=Nat.one_le_pow _ _ spos
  refine ⟨readTime+1+(checkTime+1+((Encoding.node.encode values[index]).length+1+1+1)),?_,
    reading.sequence (checking.sequence (clearing.sequence pushing))⟩
  change _≤200000*S^5
  dsimp only [S] at *
  omega

end Counting.StackMachine.DagValidation
