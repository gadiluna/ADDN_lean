import Counting.StackDagNodesAll

/-! Read the actual serialized node-table header and check all its semantic
node conditions. Canonical serialization is a separate VerifiedParser gate;
no free list decoding or iteration over an externally supplied count occurs. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def nodesPrefixHeaderRoles : FullListWorkspace 18:=
  ⟨![17,1,0,2,27,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩

def nodesPrefixRoutine : Routine 33:=sequence (readListHeader 18 nodesPrefixHeaderRoles) allNodesFromCount

def nodesPrefixStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (suffix : List Bool) : Store 33:=
  Function.update (Function.update store 17 (Encoding.sequence Encoding.node values++suffix)) 1
    ((accepted && nodeRangeCheck values 0 values.length)::tail)

theorem nodesPrefix_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (suffix : List Bool)
    (source : store 17=(Encoding.list Encoding.node).encode values++suffix) :
    ∃ time ≤ 222000000*((store 17).length+1)^6,
      Executes nodesPrefixRoutine store time (nodesPrefixStore store accepted tail values suffix) := by
  have positive (node : Executable.Node) : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (nodesPrefixHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [nodesPrefixHeaderRoles,work,extraWork]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 18 nodesPrefixHeaderRoles store accepted tail
    status headerWork Encoding.node positive values suffix source
  let ready:=Function.update (Function.update store 17 (Encoding.sequence Encoding.node values++suffix))
    27 (List.replicate values.length true)
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n17 : r≠17:=by intro eq;subst r;norm_num at small
    have n27 : r≠27:=by intro eq;subst r;norm_num at small
    simp [ready,n17,n27,work r small ne]
  have readyExtra (r : Fin 35) (member : r∈({18,19,20,21,22,23,24,25,26,28,29,30,31,32,33,34}:Finset (Fin 35))) : ready r=[]:=by
    have n17 : r≠17:=by intro eq;subst r;exact (by decide : (17:Fin 35)∉({18,19,20,21,22,23,24,25,26,28,29,30,31,32,33,34}:Finset (Fin 35))) member
    have n27 : r≠27:=by intro eq;subst r;exact (by decide : (27:Fin 35)∉({18,19,20,21,22,23,24,25,26,28,29,30,31,32,33,34}:Finset (Fin 35))) member
    have original : r∈({18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34}:Finset (Fin 35)):=by
      simp only [Finset.mem_insert,Finset.mem_singleton] at member ⊢
      tauto
    simp [ready,n17,n27,extraWork r original]
  obtain ⟨checkTime,checkBound,checkRun⟩:=allNodesFromCount_executes ready accepted tail
    (by simp [ready,status]) readyWork readyExtra values suffix (by simp [ready]) (by simp [ready])
  have final : Function.update (Function.update ready 27 []) 1
      ((accepted && nodeRangeCheck values 0 values.length)::tail)=nodesPrefixStore store accepted tail values suffix:=by
    funext r
    by_cases r1 : r=1
    · subst r;simp [nodesPrefixStore]
    · by_cases r27 : r=27
      · subst r;simp [nodesPrefixStore,extraWork]
      · simp [ready,nodesPrefixStore,r1,r27]
  rw [final] at checkRun
  have readyLength : (ready 17).length≤(store 17).length:=by
    rw [source]
    change (Encoding.sequence Encoding.node values++suffix).length≤
      ((Encoding.natural.encode values.length++Encoding.sequence Encoding.node values)++suffix).length
    simp only [List.length_append]
    omega
  have checkLimit : checkTime≤221000000*((store 17).length+1)^6:=by apply checkBound.trans;gcongr
  change headerTime≤1820*((store 17).length+1)^3 at headerBound
  have cube : ((store 17).length+1)^3≤((store 17).length+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have one : 1≤((store 17).length+1)^6:=Nat.one_le_pow _ _ (by omega)
  exact ⟨headerTime+1+checkTime,by omega,headerRun.sequence checkRun⟩

end Counting.StackMachine.DagValidation
