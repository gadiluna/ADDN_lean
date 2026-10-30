import Counting.StackDagCoverCount
import Counting.StackDagCoverCriterion

/-! The complete closure component reads the explicit table cardinality,
checks every non-final target, reads the actual bottom field and rejects
empty tables. It never loops to an untrusted binary index. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def coverPrefixHeaderRoles : FullListWorkspace 18:=
  ⟨![17,1,0,2,25,3,8,9,4,10,11,5,6,7,12,13,14],by decide⟩

def coverPrefix : Routine 33:=sequence (readListHeader 18 coverPrefixHeaderRoles)
  (sequence coverFromCount (clear 25))

def coverPrefixStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (bottom : Nat) : Store 33:=
  Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++Encoding.natural.encode bottom))
    1 ((accepted && coverCheck nodes bottom)::tail)

theorem coverPrefix_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,24,25,26,27,28,30,31,34}:Finset (Fin 35)) → store r=[])
    (nodes : List Executable.Node) (bottom : Nat)
    (source : store 17=(Encoding.list Encoding.node).encode nodes++Encoding.natural.encode bottom) :
    ∃ time ≤ 103000*((store 17).length+1)^5,
      Executes coverPrefix store time (coverPrefixStore store accepted tail nodes bottom) := by
  have positive (node : Executable.Node) : 0<(Encoding.node.encode node).length:=by
    rw [Encoding.node_length]
    unfold Encoding.nodeBits
    omega
  have headerWork (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (coverPrefixHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [coverPrefixHeaderRoles,work,extraWork]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 18 coverPrefixHeaderRoles store accepted tail
    status headerWork Encoding.node positive nodes (Encoding.natural.encode bottom) source
  let ready:=Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes++Encoding.natural.encode bottom))
    25 (List.replicate nodes.length true)
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n17 : r≠17:=by intro eq;subst r;norm_num at small
    have n25 : r≠25:=by intro eq;subst r;norm_num at small
    simp [ready,n17,n25,work r small ne]
  have readyExtra (r : Fin 35) (member : r∈({21,22,23,24,26,27,28,30,31,34}:Finset (Fin 35))) : ready r=[]:=by
    have n17 : r≠17:=by intro eq;subst r;exact (by decide : (17:Fin 35)∉({21,22,23,24,26,27,28,30,31,34}:Finset (Fin 35))) member
    have n25 : r≠25:=by intro eq;subst r;exact (by decide : (25:Fin 35)∉({21,22,23,24,26,27,28,30,31,34}:Finset (Fin 35))) member
    have original : r∈({21,22,23,24,25,26,27,28,30,31,34}:Finset (Fin 35)):=by
      simp only [Finset.mem_insert,Finset.mem_singleton] at member ⊢
      tauto
    simp [ready,n17,n25,extraWork r original]
  obtain ⟨checkTime,checkBound,checkRun⟩:=coverFromCount_executes ready accepted tail
    (by simp [ready,status]) readyWork readyExtra nodes bottom (by simp [ready]) (by simp [ready])
  let checked:=Function.update ready 1 ((accepted && coverCheck nodes bottom)::tail)
  have clearing:=clear_executes (25:Fin 35) checked
  have counter : checked 25=List.replicate nodes.length true:=by simp [checked,ready]
  rw [counter,List.length_replicate] at clearing
  have final : Function.update checked 25 []=coverPrefixStore store accepted tail nodes bottom:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r17 : r=17 <;> by_cases r25 : r=25 <;>
      simp [checked,ready,coverPrefixStore,r1,r17,r25,extraWork]
  rw [final] at clearing
  have readyLength : (ready 17).length≤(store 17).length:=by
    rw [source]
    change (Encoding.sequence Encoding.node nodes++Encoding.natural.encode bottom).length≤
      ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++Encoding.natural.encode bottom).length
    simp only [List.length_append]
    omega
  have nodeLength : nodes.length≤(store 17).length:=by
    have count:=node_sequence_count_le nodes
    rw [source]
    change nodes.length≤((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++Encoding.natural.encode bottom).length
    simp only [List.length_append]
    omega
  have checkLimit : checkTime≤100000*((store 17).length+1)^5:=by apply checkBound.trans;gcongr
  change headerTime≤1820*((store 17).length+1)^3 at headerBound
  have cube : ((store 17).length+1)^3≤((store 17).length+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have linear : (store 17).length+1≤((store 17).length+1)^5:=Nat.le_self_pow (by decide) _
  exact ⟨headerTime+1+(checkTime+1+(nodes.length+1)),by omega,headerRun.sequence (checkRun.sequence clearing)⟩

theorem coverCheck_eq_closure (vista : Executable.Vista) (nodes : Executable.NodesValid vista)
    (inside : vista.bottom<vista.nodes.size) :
    coverCheck vista.nodes.toList vista.bottom=(Executable.closure vista).all id:=by
  simpa only [coverCheck,Array.length_toList] using coverRange_eq_closure_all vista nodes inside

end Counting.StackMachine.DagValidation
