import Counting.StackDagNodeCheck

/-! Semantic checking after actual indexed node extraction. The serialized
DAG, unary index and its binary encoding are preserved; only status changes.
This is the reusable body for checking every node in a finite DAG. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def nodeAtReadRoles : Fin 20 ↪ Fin 35 where
  toFun r:=if r.val<18 then ⟨r.val,by omega⟩ else if r=18 then 29 else 28
  inj':=by intro a b equal;fin_cases a <;> fin_cases b <;> simp_all

def nodeAtRoutine : Routine 33:=sequence (mapRegisters nodeAtReadRoles DagParser.preservingNodeRead) nodeCheckRoutine

theorem nodeAt_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (index : Fin values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (currentBits : store 24=index.val.bits) (budget : (store 29).length=index.val) :
    ∃ time ≤ 220000000*((store 17).length+1)^5,
      Executes nodeAtRoutine store time
        (Function.update store 1 ((accepted && nodeCondition values index.val values[index])::tail)) := by
  let localStore : Store 18:=store ∘ nodeAtReadRoles
  have localWork (r : Fin 17) (ne : r≠1) : localStore (DagParser.nodeRoles r)=[]:=by
    have small : r.val<18:=by have:=r.isLt;omega
    have rsmall : (nodeAtReadRoles (DagParser.nodeRoles r)).val<17:=by
      simp [nodeAtReadRoles,DagParser.nodeRoles,small]
    have rne : nodeAtReadRoles (DagParser.nodeRoles r)≠1:=by
      intro eq;apply ne;apply Fin.ext
      simpa [nodeAtReadRoles,small,DagParser.nodeRoles] using congrArg (fun r:Fin 35=>r.val) eq
    exact work _ rsmall rne
  obtain ⟨readTime,readBound,readRun⟩:=DagParser.preservingNodeRead_get localStore accepted tail
    (by simp [localStore,nodeAtReadRoles,status]) localWork
    (by simp [localStore,nodeAtReadRoles,extraWork]) values index sourceSuffix
    (by simp [localStore,nodeAtReadRoles,source])
    (by simp [localStore,nodeAtReadRoles,budget])
  let readStore:=Function.update store 28 (Encoding.node.encode values[index])
  have relocated : Executes (mapRegisters nodeAtReadRoles DagParser.preservingNodeRead) store readTime readStore:=by
    apply relocate_executes_frame DagParser.preservingNodeRead nodeAtReadRoles store readStore localStore
      (Function.update localStore 19 (Encoding.node.encode values[index])) readTime rfl _ _ readRun
    · intro r;fin_cases r <;> simp [readStore,localStore,nodeAtReadRoles]
    · intro r outside
      have n28 : r≠28:=by intro eq;subst r;exact outside 19 rfl
      simp [readStore,n28]
  have readWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : readStore r=[]:=by
    have n28 : r≠28:=by intro eq;subst r;norm_num at small
    simp [readStore,n28,work r small ne]
  have readExtra (r : Fin 35) (member : r∈({18,19,20,21,22,23,25,26,30,31,32,33,34}:Finset (Fin 35))) : readStore r=[]:=by
    have n28 : r≠28:=by
      intro eq;subst r
      exact (by decide : (28:Fin 35)∉({18,19,20,21,22,23,25,26,30,31,32,33,34}:Finset (Fin 35))) member
    have original : r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35)):=by
      simp only [Finset.mem_insert,Finset.mem_singleton] at member ⊢
      tauto
    simp [readStore,n28,extraWork r original]
  obtain ⟨checkTime,checkBound,checkRun⟩:=nodeCheck_executes readStore accepted tail
    (by simp [readStore,status]) readWork readExtra values index.val values[index] index.isLt sourceSuffix
    (by simp [readStore,source]) (by simp [readStore,currentBits]) (by simp [readStore,budget])
    (by simp [readStore])
  have restored : nodeCheckStore readStore accepted tail values index.val values[index]=
      Function.update store 1 ((accepted && nodeCondition values index.val values[index])::tail):=by
    funext r
    by_cases r1 : r=1
    · subst r;simp [nodeCheckStore]
    · by_cases r28 : r=28
      · subst r;simp [nodeCheckStore,extraWork]
      · simp [nodeCheckStore,readStore,r1,r28]
  rw [restored] at checkRun
  have readSource : localStore 17=store 17:=by simp [localStore,nodeAtReadRoles]
  have readIndex : (localStore 18).length=index.val:=by simp [localStore,nodeAtReadRoles,budget]
  rw [readSource,readIndex] at readBound
  have checkSource : readStore 17=store 17:=by simp [readStore]
  have checkInput : readStore 28=Encoding.node.encode values[index]:=by simp [readStore]
  rw [checkSource,checkInput] at checkBound
  have count:=node_sequence_count_le values
  have member:=node_sequence_member_le values values[index] (List.getElem_mem index.isLt)
  have indexBound : index.val≤(store 17).length:=by rw [source,List.length_append];have:=index.isLt;omega
  have nodeLength : (Encoding.node.encode values[index]).length≤(store 17).length:=by rw [source,List.length_append];omega
  have indexSize : index.val.size≤ index.val:=Nat.size_le.mpr Nat.lt_two_pow_self
  let S:=(store 17).length+1
  have positiveS : 1≤S:=by dsimp only [S];omega
  have base : (store 17).length+(Encoding.node.encode values[index]).length+index.val.size+1≤3*S:=by dsimp only [S];omega
  have checkLimit : checkTime≤218943000*S^5:=by
    calc
      checkTime≤901000*(3*S)^5:=checkBound.trans (by gcongr)
      _=218943000*S^5:=by ring
  have factor : 2*index.val+3≤3*S:=by dsimp only [S];omega
  have readLimit : readTime≤6100*S^4+14:=by
    have bounded : readTime≤6087*S^4+13*(store 17).length+14:=by
      have part : (2*index.val+3)*2029*((store 17).length+1)^3≤6087*S^4:=by
        calc
          _≤(3*S)*2029*S^3:=by gcongr
          _=6087*S^4:=by ring
      omega
    have linear : S≤S^4:=Nat.le_self_pow (by decide) _
    dsimp [S] at bounded linear ⊢
    omega
  have fourth : S^4≤S^5:=Nat.pow_le_pow_right positiveS (by decide)
  have fifth : 1≤S^5:=Nat.one_le_pow _ _ positiveS
  exact ⟨readTime+1+checkTime,by change _≤220000000*S^5;omega,relocated.sequence checkRun⟩

end Counting.StackMachine.DagValidation
