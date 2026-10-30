import Counting.NetworkRecognitionRounds

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def roundsHeaderRoles : FullListWorkspace 9 := ⟨![17,1,3,4,25,5,8,9,6,10,11,7,12,13,14,15,16],by decide⟩
def roundsPrefix : Routine 24 := sequence (readListHeader 9 roundsHeaderRoles) (forEach 25 matrixCheck)

def roundsPrefixStore (store:Store 24) (accepted:Bool) (tail:List Bool)
    (graphs:List (List (List Nat))) (suffix:List Bool) : Store 24 :=
  Function.update (Function.update store 17 suffix) 1 ((accepted && roundDecisions (store 0).length graphs)::tail)

theorem roundsPrefix_executes (store:Store 24) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r:Fin 26,r≠0 → r≠1 → r≠17 → store r=[])
    (unary:store 0=List.replicate (store 0).length true)
    (graphs:List (List (List Nat))) (suffix:List Bool)
    (input:store 17=(Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode graphs++suffix) :
    ∃time ≤ 500020000*((store 17).length+(store 0).length+1)^7,
      Executes roundsPrefix store time (roundsPrefixStore store accepted tail graphs suffix) := by
  have positive (graph:List (List Nat)) : 0<((Encoding.list (Encoding.list Encoding.natural)).encode graph).length := by
    change 0<(Encoding.natural.encode graph.length++Encoding.sequence (Encoding.list Encoding.natural) graph).length
    rw [List.length_append,Encoding.natural_length];omega
  have headerWork (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (roundsHeaderRoles i)=[] := by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [roundsHeaderRoles,work]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 9 roundsHeaderRoles store accepted tail status headerWork
    (Encoding.list (Encoding.list Encoding.natural)) positive graphs suffix input
  let ready:=Function.update (Function.update store 17
    (Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs++suffix)) 25 (List.replicate graphs.length true)
  obtain ⟨loopTime,loopBound,loopRun⟩:=rounds_executes ready accepted tail (by simp [ready,status])
    (by intro r n0 n1 n17 n25;simpa [ready,n17,n25] using work r n0 n1 n17)
    (by simpa [ready] using unary) graphs suffix (by simp [ready]) (by simp [ready])
  have final:roundsStore ready accepted tail graphs suffix=roundsPrefixStore store accepted tail graphs suffix:=by
    funext r
    by_cases n1:r=1 <;> by_cases n17:r=17 <;> by_cases n25:r=25 <;>
      simp [roundsStore,ready,roundsPrefixStore,n1,n17,n25,work]
  rw [final] at loopRun
  have shorter:(ready 17).length ≤ (store 17).length:=by
    rw [input]
    change (Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs++suffix).length ≤
      ((Encoding.natural.encode graphs.length++Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs)++suffix).length
    simp only [List.length_append];omega
  have countBound:graphs.length ≤ (store 17).length:=by
    have count:=VerifiedParser.sequence_count_le positive graphs
    rw [input]
    change _ ≤ ((Encoding.natural.encode graphs.length++Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) graphs)++suffix).length
    simp only [List.length_append];omega
  let S:=(store 17).length+(store 0).length+1
  have base:S=(store 17).length+(store 0).length+1:=rfl
  have positiveS:1≤S:=by omega
  have headerLimit:headerTime ≤ 1820*S^3:=by
    apply headerBound.trans
    change 1820*((store 17).length+1)^3 ≤ _
    gcongr;omega
  rw [show ready 0=store 0 by simp [ready]] at loopBound
  have loopLimit:loopTime ≤ S*(500010000*S^6+2)+1:=by apply loopBound.trans;gcongr <;> omega
  have lower:S^3≤S^7:=Nat.pow_le_pow_right positiveS (by decide)
  have linear:S≤S^7:=Nat.le_self_pow (by decide) _
  have one:1≤S^7:=Nat.one_le_pow _ _ positiveS
  refine ⟨headerTime+1+loopTime,?_,headerRun.sequence loopRun⟩
  change _ ≤ 500020000*S^7
  nlinarith

end Counting.StackMachine.NetworkRecognition
