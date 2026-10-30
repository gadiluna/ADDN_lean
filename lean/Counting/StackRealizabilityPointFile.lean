import Counting.StackRealizabilityMassCalculate
import Counting.StackRealizabilityWeightLookup

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The first 42 cells are the mass-scan workspace. The remaining 18 cells
hold loop counters, numerical context and accumulated graph fields. -/
def pointFile (base : Store 40) (data : Fin 18→List Bool) : Store 58 :=
  fun r => if small : r.val<42 then base ⟨r.val,small⟩ else data ⟨r.val-42,by omega⟩

def pointCoreRoles : Fin 42 ↪ Fin 60 where
  toFun r := ⟨r.val,by omega⟩
  inj' := by intro a b same;apply Fin.ext;exact congrArg (fun r : Fin 60 => r.val) same

def pointExtraRoles : Fin 18 ↪ Fin 60 where
  toFun r := ⟨r.val+42,by omega⟩
  inj' := by
    intro a b same
    apply Fin.ext
    have equal := congrArg (fun r : Fin 60 => r.val) same
    change a.val+42=b.val+42 at equal
    omega

@[simp] theorem pointFile_core (base : Store 40) (data : Fin 18→List Bool) (r : Fin 42) :
    pointFile base data (pointCoreRoles r)=base r := by simp [pointFile,pointCoreRoles]

@[simp] theorem pointFile_extra (base : Store 40) (data : Fin 18→List Bool) (r : Fin 18) :
    pointFile base data (pointExtraRoles r)=data r := by simp [pointFile,pointExtraRoles]

theorem pointFile_update_data (base : Store 40) (data : Fin 18→List Bool) (r : Fin 18) (value : List Bool) :
    Function.update (pointFile base data) (pointExtraRoles r) value=
      pointFile base (Function.update data r value) := by
  funext i
  by_cases small : i.val<42
  · have different : i≠pointExtraRoles r := by
      intro same
      have equal := congrArg (fun i : Fin 60 => i.val) same
      change i.val=r.val+42 at equal
      omega
    simp [pointFile,small,different]
  · by_cases same : i=pointExtraRoles r
    · subst i
      simp
    · have different : (⟨i.val-42,by omega⟩:Fin 18)≠r := by
        intro equal
        apply same
        apply Fin.ext
        have values := congrArg (fun i : Fin 18 => i.val) equal
        change i.val-42=r.val at values
        change i.val=r.val+42
        omega
      simp [pointFile,small,same,different]

def pointCalculate : Routine 58 := mapRegisters pointCoreRoles massCalculate

theorem pointCalculate_executes (source weights : List Bool) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old : Nat) (data : Fin 18→List Bool) :
    ∃ time ≤ 100000000*(source.length+weights.length+target.size+old.size+2)^15,
      Executes pointCalculate
        (pointFile (massFile source weights target.bits [] old.bits (accepted::tail) [] [] []) data) time
        (pointFile (massFile source weights target.bits [] old.bits (accepted::tail)
          (childRangeSum nodes target old 0 values).bits
          (demandRangeSum nodes target old 0 values).bits
          (supplyRangeSum nodes target old 0 values).bits) data) := by
  obtain ⟨time,bound,run⟩ := massCalculate_executes source weights accepted tail nodes sorted values length
    nodeSuffix weightSuffix nodeInput weightInput target old
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame massCalculate pointCoreRoles _ _ _ _ time _ _ _ run
  · funext r;simp
  · intro r;simp
  · intro r outside
    have large : ¬r.val<42 := by
      intro small
      exact outside ⟨r.val,small⟩ (Fin.ext rfl)
    simp [pointFile,large]

def pointWeightRoles : Fin 8 ↪ Fin 60 := ⟨![35,42,43,40,0,2,3,4],by decide⟩
def pointWeight : Routine 58 := weightLookup 52 pointWeightRoles

theorem pointWeight_executes (source level parent query status child accumulator saved : List Bool)
    (values : List Nat) (data : Fin 18→List Bool) (empty : data 1=[]) :
    ∃ time ≤ 10*((Encoding.list Encoding.natural).encode values).length+8*(data 0).length+28,
      Executes pointWeight
        (pointFile (massFile source ((Encoding.list Encoding.natural).encode values) level parent query
          status child accumulator saved) data) time
        (pointFile (massFile source ((Encoding.list Encoding.natural).encode values) level parent query
          status child accumulator saved) (Function.update data 1 (values[(data 0).length]?.getD 0).bits)) := by
  let base := massFile source ((Encoding.list Encoding.natural).encode values) level parent query status child accumulator saved
  let store := pointFile base data
  obtain ⟨time,bound,run⟩ := weightLookup_executes 52 pointWeightRoles store values
    (by simp [store,base,pointFile,massFile,pointWeightRoles])
    (by simp [store,base,pointFile,massFile,pointWeightRoles])
    (by simp [store,base,pointFile,massFile,pointWeightRoles])
    (by simp [store,base,pointFile,massFile,pointWeightRoles])
    (by simp [store,base,pointFile,massFile,pointWeightRoles])
  have sourceAt : store (pointWeightRoles 0)=((Encoding.list Encoding.natural).encode values) := by
    simp [store,base,pointFile,massFile,pointWeightRoles]
  have indexAt : store (pointWeightRoles 1)=data 0 := by simp [store,pointFile,pointWeightRoles]
  have outputAt : store (pointWeightRoles 2)=[] := by simp [store,pointFile,pointWeightRoles,empty]
  rw [sourceAt,indexAt] at bound
  rw [indexAt,outputAt,List.append_nil] at run
  change Executes pointWeight store time
    (Function.update (pointFile base data) (pointExtraRoles 1) (values[(data 0).length]?.getD 0).bits) at run
  rw [pointFile_update_data] at run
  exact ⟨time,bound,run⟩

end Counting.StackMachine.RealizabilityCheck
