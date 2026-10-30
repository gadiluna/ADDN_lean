import Counting.StackRealizabilityRoundFile
import Counting.StackRealizabilityPointVisible

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000

def roundPointRoles : Fin 60 ↪ Fin 100 := ⟨![0,85,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,84,23,24,25,26,27,28,29,30,31,32,33,80,81,36,37,38,39,40,41,42,43,82,96,46,47,91,92,50,51,88,87,54,55,56,57,58,59],by decide⟩

def roundPointData (data : Fin 20→List Bool) : Fin 18→List Bool := fun r =>
  if r=2 then data 2 else if r=3 then data 16 else if r=6 then data 11 else if r=7 then data 12
  else if r=10 then data 8 else if r=11 then data 7 else []

theorem roundPoint_store (data : Fin 20→List Bool) (nodes : List Executable.Node) (values : List Nat)
    (target : Nat) (status : List Bool)
    (input : data 0=(Encoding.list Encoding.node).encode nodes)
    (weights : data 1=(Encoding.list Encoding.natural).encode values)
    (level : data 4=target.bits) (statusAt : data 5=status) :
    roundFile data ∘ roundPointRoles=
      pointLoopStore nodes values target 0 status (roundPointData data) [] [] [] [] := by
  funext r
  fin_cases r <;> simp [roundFile,roundPointRoles,pointLoopStore,pointFile,massFile,pointLoopData,
    roundPointData,input,weights,level,statusAt]

def roundVisible : Routine 98 := mapRegisters roundPointRoles pointVisible

theorem roundVisible_executes (data : Fin 20→List Bool) (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length) (target : Nat) (accepted : Bool) (tail : List Bool)
    (input : data 0=(Encoding.list Encoding.node).encode nodes)
    (weights : data 1=(Encoding.list Encoding.natural).encode values)
    (level : data 4=target.bits) (status : data 5=accepted::tail) (empty : data 16=[]) :
    ∃ time ≤ 15000*(massInputSize nodes values+target.size)^5,
      Executes roundVisible (roundFile data) time
        (roundFile (Function.update data 16 (levelRangeSum nodes target 0 values).bits)) := by
  obtain ⟨time,bound,run⟩ := pointVisible_executes nodes values length target accepted tail
    (roundPointData data) (by simp [roundPointData,empty])
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame pointVisible roundPointRoles (roundFile data) _ _ _ time
    (roundPoint_store data nodes values target _ input weights level status) _ _ run
  · intro r
    fin_cases r <;> simp [roundFile,roundPointRoles,pointLoopStore,pointFile,massFile,pointLoopData,
      roundPointData,input,weights,level,status]
  · intro r outside
    have different : r≠96 := by intro same;subst r;exact outside 45 rfl
    rw [←roundFile_update]
    exact Function.update_of_ne different _ _

def roundPointTables : Routine 98 := mapRegisters roundPointRoles pointTables

def roundPointTablesData (data : Fin 20→List Bool) (nodes : List Executable.Node) (values : List Nat)
    (target order visible : Nat) (accepted : Bool) (tail : List Bool) : Fin 20→List Bool :=
  Function.update (Function.update (Function.update data 5
    ((accepted && pointRangeCheck nodes values (data 8) target order visible 0 (data 7).length)::tail))
    11 (leavingRangeValues nodes values target 0 (data 7).length))
    12 (deficitRangeValues nodes values target 0 (data 7).length)

theorem roundPointTablesFile (data : Fin 20→List Bool) (nodes : List Executable.Node) (values : List Nat)
    (target order visible : Nat) (accepted : Bool) (tail : List Bool) :
    roundFile (roundPointTablesData data nodes values target order visible accepted tail)=
      Function.update (Function.update (Function.update (roundFile data) 85
        ((accepted && pointRangeCheck nodes values (data 8) target order visible 0 (data 7).length)::tail))
        91 (leavingRangeValues nodes values target 0 (data 7).length))
        92 (deficitRangeValues nodes values target 0 (data 7).length) := by
  change _=Function.update (Function.update (Function.update (roundFile data) (roundContext 5) _)
    (roundContext 11) _) (roundContext 12) _
  rw [roundFile_update,roundFile_update,roundFile_update]
  rfl

theorem roundPointTables_executes (data : Fin 20→List Bool) (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length) (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (target order visible : Nat) (accepted : Bool) (tail : List Bool)
    (input : data 0=(Encoding.list Encoding.node).encode nodes)
    (weights : data 1=(Encoding.list Encoding.natural).encode values)
    (level : data 4=target.bits) (status : data 5=accepted::tail)
    (orderAt : data 2=order.bits) (visibleAt : data 16=visible.bits)
    (e11 : data 11=[]) (e12 : data 12=[]) :
    ∃ time ≤ 300000000*(massInputSize nodes values+target.size+order.size+visible.size+
        (data 8).length+2*(data 7).length+2)^16,
      Executes roundPointTables (roundFile data) time
        (roundFile (roundPointTablesData data nodes values target order visible accepted tail)) := by
  obtain ⟨time,bound,run⟩ := pointTables_executes nodes values length sorted target order visible
    accepted tail (roundPointData data) (by simp [roundPointData])
    (by simp [roundPointData,orderAt]) (by simp [roundPointData,visibleAt])
    (by simp [roundPointData,e11]) (by simp [roundPointData,e12]) (by simp [roundPointData])
  refine ⟨time,by simpa [pointTablesSize,roundPointData] using bound,?_⟩
  apply relocate_executes_frame pointTables roundPointRoles (roundFile data) _ _ _ time
    (roundPoint_store data nodes values target _ input weights level status) _ _ run
  · intro r
    fin_cases r <;> simp [roundFile,roundPointRoles,pointLoopStore,pointFile,massFile,pointLoopData,
      roundPointData,roundPointTablesData,input,weights,level]
  · intro r outside
    have n85 : r≠85 := by intro same;subst r;exact outside 1 rfl
    have n91 : r≠91 := by intro same;subst r;exact outside 48 rfl
    have n92 : r≠92 := by intro same;subst r;exact outside 49 rfl
    rw [roundPointTablesFile]
    simp [n85,n91,n92]

end Counting.StackMachine.RealizabilityCheck
