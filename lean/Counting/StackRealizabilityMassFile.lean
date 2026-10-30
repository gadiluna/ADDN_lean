import Counting.StackRealizabilityChildPreserved
import Counting.StackRealizabilitySupplyPreserved
import Counting.StackRealizabilityDemandPreserved

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def massFile (source weights level parent query status child accumulator saved : List Bool) : Store 40 :=
  fun r => if r=1 then status else if r=21 then child else if r=22 then level
    else if r=25 then parent else if r=26 then accumulator else if r=34 then source
    else if r=35 then weights else if r=36 then query else if r=37 then saved else []

def massRoles : Fin 36 ↪ Fin 42 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b same;apply Fin.ext;exact congrArg (fun r : Fin 42 => r.val) same

def massChild : Routine 40 := mapRegisters massRoles childPreserved
def massSupply : Routine 40 := mapRegisters massRoles supplyPreserved
def massDemand : Routine 40 := mapRegisters massRoles demandPreserved

theorem massChild_executes (source weights query saved : List Bool)
    (accepted : Bool) (tail : List Bool) (nodes : List Executable.Node)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old total : Nat) :
    ∃ time ≤ 15000*(source.length+weights.length+total.size+target.size+(old+1).size+1)^5,
      Executes massChild (massFile source weights target.bits (old+1).bits query (accepted::tail) total.bits [] saved) time (massFile source weights target.bits (old+1).bits query (accepted::tail) (total+childRangeSum nodes target old 0 values).bits [] saved) := by
  let original := massFile source weights target.bits (old+1).bits query (accepted::tail) total.bits [] saved
  let localStore : Store 34 := original ∘ massRoles
  have work (r : Fin 36) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,original,massFile,massRoles]
  obtain ⟨time,bound,run⟩ := childPreserved_executes localStore accepted tail
    (by simp [localStore,original,massFile,massRoles]) work
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    nodes values length nodeSuffix weightSuffix
    (by simpa [localStore,original,massFile,massRoles] using nodeInput)
    (by simpa [localStore,original,massFile,massRoles] using weightInput)
    target old total
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
  refine ⟨time,by simpa [localStore,original,massFile,massRoles] using bound,?_⟩
  apply relocate_executes_frame childPreserved massRoles original _ localStore _ time rfl _ _ run
  · intro r
    fin_cases r <;> simp [original,localStore,massFile,massRoles]
  · intro r outside
    have different : r≠21 := by intro same;subst r;exact outside 21 rfl
    simp [original,massFile,different]

theorem massSupply_executes (source weights query child saved : List Bool)
    (accepted : Bool) (tail : List Bool) (nodes : List Executable.Node)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old total : Nat) :
    ∃ time ≤ 1800000*(source.length+weights.length+total.size+target.size+(old+1).size+1)^9,
      Executes massSupply (massFile source weights target.bits (old+1).bits query (accepted::tail) child total.bits saved) time (massFile source weights target.bits (old+1).bits query (accepted::tail) child (total+supplyRangeSum nodes target old 0 values).bits saved) := by
  let original := massFile source weights target.bits (old+1).bits query (accepted::tail) child total.bits saved
  let localStore : Store 34 := original ∘ massRoles
  have work (r : Fin 36) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,original,massFile,massRoles]
  obtain ⟨time,bound,run⟩ := supplyPreserved_executes localStore accepted tail
    (by simp [localStore,original,massFile,massRoles]) work
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    nodes values length nodeSuffix weightSuffix
    (by simpa [localStore,original,massFile,massRoles] using nodeInput)
    (by simpa [localStore,original,massFile,massRoles] using weightInput)
    target old total
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
  refine ⟨time,by simpa [localStore,original,massFile,massRoles] using bound,?_⟩
  apply relocate_executes_frame supplyPreserved massRoles original _ localStore _ time rfl _ _ run
  · intro r
    fin_cases r <;> simp [original,localStore,massFile,massRoles]
  · intro r outside
    have different : r≠26 := by intro same;subst r;exact outside 26 rfl
    simp [original,massFile,different]

theorem massDemand_executes (source weights query child saved : List Bool)
    (accepted : Bool) (tail : List Bool) (nodes : List Executable.Node)
    (sorted : ∀node∈nodes, Executable.countsSorted node.incoming=true)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old total : Nat) :
    ∃ time ≤ 94000000*(source.length+weights.length+total.size+target.size+old.size+1)^15,
      Executes massDemand (massFile source weights target.bits old.bits query (accepted::tail) child total.bits saved) time (massFile source weights target.bits old.bits query (accepted::tail) child (total+demandRangeSum nodes target old 0 values).bits saved) := by
  let original := massFile source weights target.bits old.bits query (accepted::tail) child total.bits saved
  let localStore : Store 34 := original ∘ massRoles
  have work (r : Fin 36) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,original,massFile,massRoles]
  obtain ⟨time,bound,run⟩ := demandPreserved_executes localStore accepted tail
    (by simp [localStore,original,massFile,massRoles]) work
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    nodes sorted values length nodeSuffix weightSuffix
    (by simpa [localStore,original,massFile,massRoles] using nodeInput)
    (by simpa [localStore,original,massFile,massRoles] using weightInput)
    target old total
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
    (by simp [localStore,original,massFile,massRoles])
  refine ⟨time,by simpa [localStore,original,massFile,massRoles] using bound,?_⟩
  apply relocate_executes_frame demandPreserved massRoles original _ localStore _ time rfl _ _ run
  · intro r
    fin_cases r <;> simp [original,localStore,massFile,massRoles]
  · intro r outside
    have different : r≠26 := by intro same;subst r;exact outside 26 rfl
    simp [original,massFile,different]

end Counting.StackMachine.RealizabilityCheck
