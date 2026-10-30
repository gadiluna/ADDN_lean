import Counting.StackAuditPrefixChildSelect
import Counting.StackDagIncrement

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev advanceParent : Routine 50 := sequence (DagValidation.incrementRoutine 49 0 32 4) (pushBit 36 true)

theorem advanceParent_executes (store : Store 50) (index : Nat)
    (e0 : store 0=[]) (e4 : store 4=[]) (current : store 32=(index+1).bits) :
    ∃ time ≤ 4*(index+1).size+9,Executes advanceParent store time
      (Function.update (Function.update store 32 (index+1+1).bits) 36 (true::store 36)) := by
  obtain ⟨time,bound,a⟩:=DagValidation.increment_natural 49 (0:Fin 52) 32 4
    (by decide) (by decide) (by decide) store e0 e4 (index+1) current
  have b:=pushBit_executes (36:Fin 52) true (Function.update store 32 (index+1+1).bits)
  have indexAt : Function.update store 32 (index+1+1).bits 36=store 36 := by simp
  rw [indexAt] at b
  exact ⟨_,by omega,a.sequence b⟩

abbrev childItem : Routine 50 := sequence childSelected advanceParent

def childItemResult (store : Store 50) (index : Nat) (present unique : Bool)
    (tailPresent tailUnique : List Bool) (predicates : Bool×Bool) : Store 50 :=
  Function.update (Function.update (childSelectedResult store present unique tailPresent tailUnique predicates)
    32 (index+1+1).bits) 36 (true::store 36)

theorem childItem_executes (store : Store 50) (vista : Executable.Vista)
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
    ∃ time ≤ 41000*((store 17).length+level.size+(level+1).size+(index.val+1).size+1)^5,
      Executes childItem store time
        (childItemResult store index.val present unique tailPresent tailUnique (childPredicates vista level index.val)) := by
  obtain ⟨selectedTime,selectedBound,a⟩:=childSelected_executes store vista index level accepted tail status work
    e18 e19 e28 e29 e31 e33 e34 e35 suffix source nodeCount indexAt parentAt levelAt childAt
    present unique tailPresent tailUnique presentAt uniqueAt
  let selected:=childSelectedResult store present unique tailPresent tailUnique (childPredicates vista level index.val)
  obtain ⟨advanceTime,advanceBound,b⟩:=advanceParent_executes selected index.val
    (by simp [selected,childSelectedResult,work]) (by simp [selected,childSelectedResult,work])
    (by simp [selected,childSelectedResult,parentAt])
  have indexSame : selected 36=store 36 := by simp [selected,childSelectedResult]
  rw [indexSame] at b
  have one : 1≤((store 17).length+level.size+(level+1).size+(index.val+1).size+1)^5 :=
    Nat.one_le_pow _ _ (by omega)
  have linear : (store 17).length+level.size+(level+1).size+(index.val+1).size+1≤
      ((store 17).length+level.size+(level+1).size+(index.val+1).size+1)^5 := Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditPrefix
