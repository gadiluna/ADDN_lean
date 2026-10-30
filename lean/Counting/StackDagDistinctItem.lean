import Counting.StackDagNodeAt
import Counting.StackDagDistinctGuard

/-! A concrete duplicate-detection step. It reads one node using the verified
indexed parser, compares canonical words without destroying either operand,
clears the selected word and advances the bounded unary index. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def distinctReadRoles : Fin 20 ↪ Fin 35 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 35=>r.val) equal

def distinctCompareRoles : Fin 6 ↪ Fin 35:=⟨![28,19,1,2,3,4],by decide⟩

def distinctItemRoutine : Routine 33:=sequence (mapRegisters distinctReadRoles DagParser.preservingNodeRead)
  (sequence (distinctGuard 29 distinctCompareRoles) (sequence (clear 19) (pushBit 18 true)))

def distinctItemStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (other current : Executable.Node) : Store 33:=
  Function.update (Function.update store 1 ((accepted && decide (current≠other))::tail)) 18 (true::store 18)

theorem distinctItem_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (output : store 19=[])
    (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (budget : (store 18).length=index.val)
    (current : Executable.Node) (currentCode : store 28=Encoding.node.encode current) :
    ∃ time ≤ 10000*((store 17).length+(store 28).length+1)^4,
      Executes distinctItemRoutine store time (distinctItemStore store accepted tail values[index] current) := by
  let localStore : Store 18:=store ∘ distinctReadRoles
  have localWork (r : Fin 17) (ne : r≠1) : localStore (DagParser.nodeRoles r)=[]:=by
    apply work
    · simp [distinctReadRoles,DagParser.nodeRoles]
    · intro eq;apply ne;apply Fin.ext
      simpa [distinctReadRoles,DagParser.nodeRoles] using congrArg (fun r:Fin 35=>r.val) eq
  obtain ⟨readTime,readBound,readRun⟩:=DagParser.preservingNodeRead_get localStore accepted tail
    (by simpa [localStore,distinctReadRoles] using status) localWork
    (by simpa [localStore,distinctReadRoles] using output) values index suffix
    (by simpa [localStore,distinctReadRoles] using source)
    (by simpa [localStore,distinctReadRoles] using budget)
  let selected:=Function.update store 19 (Encoding.node.encode values[index])
  have reading : Executes (mapRegisters distinctReadRoles DagParser.preservingNodeRead) store readTime selected:=by
    apply relocate_executes_frame DagParser.preservingNodeRead distinctReadRoles store selected localStore
      (Function.update localStore 19 (Encoding.node.encode values[index])) readTime rfl _ _ readRun
    · intro r;fin_cases r <;> simp [selected,localStore,distinctReadRoles]
    · intro r outside
      have ne : r≠19:=by intro eq;subst r;exact outside 19 rfl
      simp [selected,ne]
  have comparing:=distinctGuard_executes 29 distinctCompareRoles selected accepted tail
    (by simp [distinctCompareRoles,selected,status])
    (by simp [distinctCompareRoles,selected,work])
    (by simp [distinctCompareRoles,selected,work])
    (by simp [distinctCompareRoles,selected,work])
  have wordPredicate : (!decide (selected (distinctCompareRoles 0)=selected (distinctCompareRoles 1)))=
      decide (current≠values[index]):=by
    simpa [selected,distinctCompareRoles,currentCode] using canonical_nodes_distinct current values[index]
  rw [wordPredicate] at comparing
  let checked:=Function.update selected 1 ((accepted && decide (current≠values[index]))::tail)
  have clearing:=clear_executes (19:Fin 35) checked
  have checkedOutput : checked 19=Encoding.node.encode values[index]:=by simp [checked,selected]
  rw [checkedOutput] at clearing
  let clean:=Function.update checked 19 []
  have pushing:=pushBit_executes (18:Fin 35) true clean
  have final : Function.update clean 18 (true::clean 18)=distinctItemStore store accepted tail values[index] current:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;>
      simp [distinctItemStore,clean,checked,selected,r1,r18,r19,output]
  rw [final] at pushing
  have compareSource : selected (distinctCompareRoles 0)=store 28:=by simp [selected,distinctCompareRoles]
  have compareOther : selected (distinctCompareRoles 1)=Encoding.node.encode values[index]:=by simp [selected,distinctCompareRoles]
  have compareBound:=Compare.preservingCost_le (selected (distinctCompareRoles 0)) (selected (distinctCompareRoles 1))
  rw [compareSource,compareOther] at compareBound
  have readSource : localStore 17=store 17:=by rfl
  have readIndex : (localStore 18).length=index.val:=budget
  rw [readSource,readIndex] at readBound
  have count:=node_sequence_count_le values
  have member:=node_sequence_member_le values values[index] (List.getElem_mem index.isLt)
  have indexBound : index.val≤(store 17).length:=by rw [source,List.length_append];have:=index.isLt;omega
  have selectedLength : (Encoding.node.encode values[index]).length≤(store 17).length:=by rw [source,List.length_append];omega
  let S:=(store 17).length+(store 28).length+1
  have spos : 1≤S:=by dsimp only [S];omega
  have factor : 2*index.val+3≤3*S:=by dsimp only [S];omega
  have inputBound : (store 17).length+1≤S:=by dsimp only [S];omega
  have readLimit : readTime≤6087*S^4+13*S+14:=by
    have leading : (2*index.val+3)*2029*((store 17).length+1)^3≤6087*S^4:=by
      calc
        _≤(3*S)*2029*S^3:=by gcongr
        _=6087*S^4:=by ring
    have input : (store 17).length≤S:=by omega
    omega
  have compareLimit : Compare.preservingCost (selected (distinctCompareRoles 0)) (selected (distinctCompareRoles 1))≤6*S+11:=by
    rw [compareSource,compareOther]
    have pair : (store 28).length+(Encoding.node.encode values[index]).length≤S:=by dsimp only [S];omega
    omega
  have selectedS : (Encoding.node.encode values[index]).length≤S:=by omega
  have power : S≤S^4:=Nat.le_self_pow (by decide) _
  refine ⟨readTime+1+(Compare.preservingCost (selected (distinctCompareRoles 0)) (selected (distinctCompareRoles 1))+7+1+
    ((Encoding.node.encode values[index]).length+1+1+1)),?_,reading.sequence (comparing.sequence (clearing.sequence pushing))⟩
  change _≤10000*S^4
  have one : 1≤S^4:=Nat.one_le_pow _ _ spos
  omega

end Counting.StackMachine.DagValidation
