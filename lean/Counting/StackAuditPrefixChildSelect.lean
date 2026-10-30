import Counting.StackAuditPrefixParent
import Counting.StackAuditPrefixChildFlags
import Counting.AuditPrefixSpec

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def childPredicates (vista : Executable.Vista) (level parent : Nat) : Bool×Bool :=
  if (vista.node parent).level=level then
    let amount:=countRange vista .child (level+1) (parent+1) 0 vista.nodes.size
    (decide (0<amount),decide (amount=1))
  else (true,true)

abbrev childSelected : Routine 50 := sequence selectParent
  (branchRoutine 35 childFlags (skip 50))

def childSelectedResult (store : Store 50) (present unique : Bool) (tailPresent tailUnique : List Bool)
    (predicates : Bool×Bool) : Store 50 :=
  Function.update (Function.update store 42 ((present && predicates.1)::tailPresent))
    43 ((unique && predicates.2)::tailUnique)

/-- A node outside the parent level contributes true to both conjunctions;
at the parent level its child predicates are obtained by an actual scan. -/
theorem childSelected_executes (store : Store 50) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (level : Nat) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 52,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (indexAt : (store 36).length=index.val) (parentAt : store 32=(index.val+1).bits)
    (levelAt : store 41=level.bits) (childAt : store 30=(level+1).bits)
    (present unique : Bool) (tailPresent tailUnique : List Bool)
    (presentAt : store 42=present::tailPresent) (uniqueAt : store 43=unique::tailUnique) :
    ∃ time ≤ 40000*((store 17).length+level.size+(level+1).size+(index.val+1).size+1)^5,
      Executes childSelected store time
        (childSelectedResult store present unique tailPresent tailUnique (childPredicates vista level index.val)) := by
  obtain ⟨selectTime,selectBound,a⟩:=selectParent_executes store vista index level accepted tail status work
    e18 e19 suffix source indexAt levelAt
  rw [e35] at a
  let tested:=Function.update store 35 [decide ((vista.node index.val).level=level)]
  have restored : Function.update tested 35 []=store := by
    simp only [tested,Function.update_idem]
    rw [←e35,Function.update_eq_self]
  let S:=(store 17).length+level.size+(level+1).size+(index.val+1).size+1
  have positive : 1≤S:=by dsimp only [S];omega
  have one : 1≤S^5:=Nat.one_le_pow _ _ positive
  have selectLimit : selectTime≤9000*S^5:=selectBound.trans
    (Nat.mul_le_mul_left 9000 ((Nat.pow_le_pow_left (by dsimp only [S];omega) 4).trans
      (Nat.pow_le_pow_right positive (by decide))))
  by_cases same:(vista.node index.val).level=level
  · obtain ⟨childTime,childBound,b⟩:=childFlags_executes store vista accepted tail status work
      e18 e19 e28 e29 e31 e33 e34 e35 suffix source nodeCount (level+1) (index.val+1)
      childAt parentAt present unique tailPresent tailUnique presentAt uniqueAt
    have branch:=branch_executes_true (35:Fin 52) childFlags (skip 50) tested _ [] childTime
      (by simp [tested,same]) (by rw [restored];exact b)
    have childLimit : childTime≤22000*S^5:=childBound.trans
      (Nat.mul_le_mul_left 22000 (Nat.pow_le_pow_left (by dsimp only [S];omega) 5))
    refine ⟨selectTime+1+(1+childTime),by change selectTime+1+(1+childTime)≤40000*S^5;omega,?_⟩
    simpa only [childSelected,childSelectedResult,childPredicates,if_pos same,childFlagsResult] using
      a.sequence branch
  · have branch:=branch_executes_false (35:Fin 52) childFlags (skip 50) tested store [] 0
      (by simp [tested,same]) (by rw [restored];exact skip_executes store)
    have final : childSelectedResult store present unique tailPresent tailUnique
        (childPredicates vista level index.val)=store := by
      simp only [childPredicates,if_neg same,childSelectedResult,Bool.and_true]
      rw [←presentAt,Function.update_eq_self,←uniqueAt,Function.update_eq_self]
    refine ⟨selectTime+1+(1+0),by change selectTime+1+(1+0)≤40000*S^5;omega,?_⟩
    rw [final]
    exact a.sequence branch

end Counting.StackMachine.AuditPrefix
