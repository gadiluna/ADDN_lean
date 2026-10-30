import Counting.StackDagInitial
import Counting.StackDagIncomingFull

/-! Initial nodes require an absent parent, zero degree and no incoming
edges. The charged branch consumes its current-node metadata workspace. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def initialNodeRoles : Fin 8 ↪ Fin 35:=⟨![21,22,28,1,0,2,3,4],by decide⟩
def initialNodeRoutine : Routine 33:=
  sequence (mapRegisters initialNodeRoles initialCheckRoutine) (sequence (clear 22) (clear 28))

def initialNodeCondition (node : Executable.Node) : Bool:=
  decide (node.level=0) && node.parent.isNone && decide (node.degree=0) && decide (node.incoming=[])

def initialNodeStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (node : Executable.Node) : Store 33:=
  Function.update (Function.update (Function.update store 22 []) 28 []) 1
    ((accepted && initialNodeCondition node)::tail)

theorem initialNode_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (node : Executable.Node) (level : store 21=node.level.bits)
    (reference : store 22=(parentCode node).bits) (input : store 28=nodeSuffix node) :
    ∃ time ≤ 400*((Encoding.node.encode node).length+1),
      Executes initialNodeRoutine store time (initialNodeStore store accepted tail node) := by
  let localStore : Store 6:=store ∘ initialNodeRoles
  have localWork (r : Fin 8) (large : 4≤r.val) : localStore r=[]:=by
    fin_cases r
    all_goals try (norm_num at large)
    all_goals simp [localStore,initialNodeRoles,work]
  have checked:=initialCheck_executes localStore accepted tail
    (by simp [localStore,initialNodeRoles,status]) localWork
  have condition : initialCheck localStore=initialNodeCondition node:=by
    apply Bool.eq_iff_iff.mpr
    have zero (n : Nat) : n.bits=[] ↔ n=0:=by
      change n.bits=Nat.bits 0 ↔ n=0
      exact Encoding.bits_injective.eq_iff
    change ((decide (store 21=[]) && decide (store 22=[]) && decide (store 28=[false,false]))=true) ↔ _
    rw [level,reference,input]
    simp only [Bool.and_eq_true,decide_eq_true_eq,zero,parentCode_zero_iff,nodeSuffix_empty_iff,
      initialNodeCondition,Option.isNone_iff_eq_none]
    tauto
  rw [condition] at checked
  let flag:=accepted && initialNodeCondition node
  let checkedStore:=Function.update store 1 (flag::tail)
  have relocated : Executes (mapRegisters initialNodeRoles initialCheckRoutine) store (initialCost localStore) checkedStore:=by
    apply relocate_executes_frame initialCheckRoutine initialNodeRoles store checkedStore localStore
      (Function.update localStore 3 (flag::tail)) (initialCost localStore) rfl _ _ checked
    · intro r;fin_cases r <;> simp [checkedStore,localStore,initialNodeRoles]
    · intro r outside
      have n1 : r≠1:=by intro eq;subst r;exact outside 3 rfl
      simp [checkedStore,n1]
  have clearParent:=clear_executes (22:Fin 35) checkedStore
  have parentValue : checkedStore 22=(parentCode node).bits:=by simp [checkedStore,reference]
  rw [parentValue,Encoding.bits_length] at clearParent
  let middle:=Function.update checkedStore 22 []
  have clearInput:=clear_executes (28:Fin 35) middle
  have suffixValue : middle 28=nodeSuffix node:=by simp [middle,checkedStore,input]
  rw [suffixValue] at clearInput
  have final : Function.update middle 28 []=initialNodeStore store accepted tail node:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r22 : r=22 <;> by_cases r28 : r=28 <;>
      simp [middle,checkedStore,initialNodeStore,r1,r22,r28,flag]
  rw [final] at clearInput
  have size:=node_metadata_size_le node
  have suffixSize:=nodeSuffix_length_le node
  have firstCost:=initialCost_le localStore
  change initialCost localStore≤100*((store 21).length+(store 22).length+(store 28).length+1) at firstCost
  rw [level,reference,input,Encoding.bits_length,Encoding.bits_length] at firstCost
  exact ⟨initialCost localStore+1+((parentCode node).size+1+1+((nodeSuffix node).length+1)),by omega,
    relocated.sequence (clearParent.sequence clearInput)⟩

theorem initialNodeCondition_vista (vista : Executable.Vista) (current : Nat)
    (initial : (vista.node current).level=0) :
    initialNodeCondition (vista.node current)=Executable.nodeValid vista current:=by
  apply Bool.eq_iff_iff.mpr
  simp [initialNodeCondition,Executable.nodeValid,initial,List.isEmpty_iff]

end Counting.StackMachine.DagValidation
