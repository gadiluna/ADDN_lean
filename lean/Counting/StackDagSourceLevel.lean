import Counting.StackDagParentLookup

/-! A red-edge source is looked up in the serialized DAG and its stored
level is compared with the destination level. No leader equality belongs
to this red-edge condition. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def sourceLevelRoles : Fin 7 ↪ Fin 28:=⟨![0,21,1,4,5,6,7],by decide⟩

def sourceLevelLookup : Routine 26:=
  sequence (mapRegisters lookupReadRoles selectedHeader) (successorGuard 21 sourceLevelRoles)

theorem sourceLevelLookup_get (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (output : store 19=[]) (values : List Executable.Node) (sourceIndex : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (index : (store 18).length=sourceIndex.val) (targetLevel : Nat)
    (level : store 21=targetLevel.bits) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+6*(Encoding.node.encode values[sourceIndex]).length+72+
        16*values[sourceIndex].level.size+6*targetLevel.size,
      Executes sourceLevelLookup store time
        (Function.update (lookupStore store values[sourceIndex]) 1
          ((accepted && decide (values[sourceIndex].level+1=targetLevel))::tail)) := by
  obtain ⟨readTime,readBound,readRun⟩:=lookupRead_get store accepted tail status work output
    values sourceIndex suffix source index
  let parsed:=lookupStore store values[sourceIndex]
  have checked:=successorGuard_executes 21 sourceLevelRoles parsed accepted tail
    (by simp [parsed,lookupStore,sourceLevelRoles,status]) (by
      intro i member
      fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
      all_goals first | contradiction | simp [parsed,lookupStore,sourceLevelRoles,work])
  have oldLevel : parsed (sourceLevelRoles 0)=values[sourceIndex].level.bits:=by
    simp [parsed,lookupStore,sourceLevelRoles]
  have newLevel : parsed (sourceLevelRoles 1)=targetLevel.bits:=by
    simp [parsed,lookupStore,sourceLevelRoles,level]
  rw [oldLevel,newLevel,successor_naturals] at checked
  have cost:=successorCost_le values[sourceIndex].level.bits targetLevel.bits
  rw [Encoding.bits_length,Encoding.bits_length] at cost
  exact ⟨_,by omega,readRun.sequence checked⟩

end Counting.StackMachine.DagValidation
