import Counting.AuditPrefixCounts
import Counting.StackEncodingBranch

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev countItem (mode : HeaderMode) : Routine 34 := sequence (selectNode mode)
  (sequence (branchRoutine 35 (pushBit 29 true) (skip 34)) (pushBit 18 true))

def itemStore (store : Store 34) (selected : Bool) : Store 34 :=
  Function.update (Function.update store 29
    (List.replicate (if selected then 1 else 0) true++store 29)) 18 (true::store 18)

/-- Selection is charged before the unary count and physical index are
incremented. The unary count never exceeds the number of inspected nodes. -/
theorem countItem_executes (mode : HeaderMode) (store : Store 34)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (nodes : List Executable.Node) (index : Fin nodes.length) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val) (level parent : Nat)
    (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 10020*((store 17).length+level.size+parent.size+1)^4,
      Executes (countItem mode) store time
        (itemStore store (nodeMatches mode nodes[index] level parent)) := by
  obtain ⟨selectTime,selectBound,a⟩:=selectNode_executes mode store accepted tail status work
    e19 e31 e33 e34 nodes index suffix input counter level parent levelAt parentAt
  let hit:=nodeMatches mode nodes[index] level parent
  let checked:=Function.update store 35 (hit::store 35)
  have restored : Function.update checked 35 []=store := by
    simp only [checked,Function.update_idem]
    rw [←e35,Function.update_eq_self]
  have positive : 1 ≤ ((store 17).length+level.size+parent.size+1)^4 :=
    Nat.one_le_pow _ _ (by omega)
  cases result:hit with
  | false=>
    have branch:=branch_executes_false (35:Fin 36) (pushBit 29 true) (skip 34) checked store [] 0
      (by simp [checked,result,e35]) (by rw [restored];exact skip_executes store)
    have push:=pushBit_executes (18:Fin 36) true store
    have combined:=a.sequence (branch.sequence push)
    refine ⟨selectTime+4,by omega,?_⟩
    change Executes _ _ _ (itemStore store hit)
    have final : itemStore store hit=Function.update store 18 (true::store 18) := by
      simp [itemStore,result]
    rw [final]
    exact combined
  | true=>
    have pushed:=pushBit_executes (29:Fin 36) true store
    have branch:=branch_executes_true (35:Fin 36) (pushBit 29 true) (skip 34) checked
      (Function.update store 29 (true::store 29)) [] 1
      (by simp [checked,result,e35]) (by rw [restored];exact pushed)
    let counted:=Function.update store 29 (true::store 29)
    have push:=pushBit_executes (18:Fin 36) true counted
    have sameIndex : counted 18=store 18 := by simp [counted]
    rw [sameIndex] at push
    have combined:=a.sequence (branch.sequence push)
    refine ⟨selectTime+5,by omega,?_⟩
    change Executes _ _ _ (itemStore store hit)
    have final : itemStore store hit=Function.update counted 18 (true::store 18) := by
      simp [itemStore,result,counted]
    rw [final]
    exact combined

end Counting.StackMachine.AuditPrefix
