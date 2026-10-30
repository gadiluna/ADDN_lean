import Counting.StackDagNodeAt

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def nodeStepRoutine : Routine 33:=
  sequence nodeAtRoutine (sequence (incrementRoutine 32 2 24 3) (pushBit 29 true))

def nodeStepStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (index : Fin values.length) : Store 33:=
  Function.update (Function.update (Function.update store 1
    ((accepted && nodeCondition values index.val values[index])::tail)) 24 (index.val+1).bits) 29 (true::store 29)

theorem nodeStep_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (index : Fin values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (currentBits : store 24=index.val.bits) (budget : (store 29).length=index.val) :
    ∃ time ≤ 220000100*((store 17).length+1)^5,
      Executes nodeStepRoutine store time (nodeStepStore store accepted tail values index) := by
  obtain ⟨checkTime,checkBound,checkRun⟩:=nodeAt_executes store accepted tail status work extraWork values index
    sourceSuffix source currentBits budget
  let checked:=Function.update store 1 ((accepted && nodeCondition values index.val values[index])::tail)
  obtain ⟨incrementTime,incrementBound,incrementRun⟩:=increment_natural 32 2 24 3
    (by decide) (by decide) (by decide) checked (by simp [checked,work]) (by simp [checked,work]) index.val
    (by simp [checked,currentBits])
  let middle:=Function.update checked 24 (index.val+1).bits
  have pushing:=pushBit_executes (29:Fin 35) true middle
  have unary : middle 29=store 29:=by simp [middle,checked]
  rw [unary] at pushing
  have count:=node_sequence_count_le values
  have indexBound : index.val≤(store 17).length:=by rw [source,List.length_append];have:=index.isLt;omega
  have indexSize : index.val.size≤ index.val:=Nat.size_le.mpr Nat.lt_two_pow_self
  have growth:=Nat.le_self_pow (by decide : 5≠0) ((store 17).length+1)
  exact ⟨checkTime+1+(incrementTime+1+1),by omega,checkRun.sequence (incrementRun.sequence pushing)⟩

end Counting.StackMachine.DagValidation
