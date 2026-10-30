import Counting.StackDagNodeInitial
import Counting.StackDagNodePositive
import Counting.StackDagEmptyGuard

/-! One concrete semantic node validator, before the separately charged
serialized-header reader. Its acceptance agrees with the actual nodeValid
predicate, including both initial and noninitial levels. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def nodeSemanticsRoutine : Routine 33:=
  sequence (emptyFlag 21 4) (branchRoutine 4 initialNodeRoutine positiveNodeRoutine)

def nodeCondition (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Bool:=
  if node.level=0 then initialNodeCondition node else positiveNodeCondition values current node

def nodeSemanticsStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Store 33:=
  Function.update (Function.update (Function.update store 22 []) 28 []) 1
    ((accepted && nodeCondition values current node)::tail)

theorem nodeSemantics_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,25,26,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) (inside : current<values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentBits : store 24=current.bits) (budget : (store 29).length=current)
    (input : store 28=nodeSuffix node) :
    ∃ time ≤ 900010*((store 17).length+(Encoding.node.encode node).length+current.size+1)^5,
      Executes nodeSemanticsRoutine store time (nodeSemanticsStore store accepted tail values current node) := by
  have emptiness:=emptyFlag_executes (21:Fin 35) 4 store
  have flagEmpty:=work 4 (by decide) (by decide)
  have test : (store 21=[]) ↔ node.level=0:=by
    rw [level]
    change node.level.bits=Nat.bits 0 ↔ node.level=0
    exact Encoding.bits_injective.eq_iff
  simp only [flagEmpty,test] at emptiness
  let tested:=Function.update store 4 [decide (node.level=0)]
  have restored : Function.update tested 4 []=store:=by
    rw [Function.update_idem,←flagEmpty,Function.update_eq_self]
  let S:=(store 17).length+(Encoding.node.encode node).length+current.size+1
  have positiveS : 1≤S:=by dsimp [S];omega
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have nodeLength : (Encoding.node.encode node).length+1≤S:=by dsimp [S];omega
  have flagCost : emptyFlagCost (store 21)≤3:=by unfold emptyFlagCost;split <;> decide
  by_cases initial : node.level=0
  · obtain ⟨time,bounded,ran⟩:=initialNode_executes store accepted tail status work node level reference input
    have final : initialNodeStore store accepted tail node=nodeSemanticsStore store accepted tail values current node:=by
      simp only [initialNodeStore,nodeSemanticsStore,nodeCondition,initial,↓reduceIte]
    rw [final] at ran
    have branch:=branch_executes_true 4 initialNodeRoutine positiveNodeRoutine tested
      (nodeSemanticsStore store accepted tail values current node) [] time
      (by simp [tested,initial]) (restored.symm ▸ ran)
    refine ⟨emptyFlagCost (store 21)+1+(1+time),?_,emptiness.sequence branch⟩
    change emptyFlagCost (store 21)+1+(1+time)≤900010*S^5
    omega
  · obtain ⟨time,bounded,ran⟩:=positiveNode_executes store accepted tail status work extraWork values current node inside
      sourceSuffix source level reference leader currentBits budget input
    have final : positiveNodeStore store accepted tail values current node=nodeSemanticsStore store accepted tail values current node:=by
      simp only [positiveNodeStore,nodeSemanticsStore,nodeCondition,initial,↓reduceIte]
    rw [final] at ran
    have branch:=branch_executes_false 4 initialNodeRoutine positiveNodeRoutine tested
      (nodeSemanticsStore store accepted tail values current node) [] time
      (by simp [tested,initial]) (restored.symm ▸ ran)
    refine ⟨emptyFlagCost (store 21)+1+(1+time),?_,emptiness.sequence branch⟩
    change time≤900000*S^5 at bounded
    change emptyFlagCost (store 21)+1+(1+time)≤900010*S^5
    omega

theorem nodeCondition_vista (vista : Executable.Vista) (current : Nat) :
    nodeCondition vista.nodes.toList current (vista.node current)=Executable.nodeValid vista current:=by
  unfold nodeCondition
  split
  · exact initialNodeCondition_vista vista current (by assumption)
  · exact positiveNodeCondition_vista vista current (by assumption)

end Counting.StackMachine.DagValidation
