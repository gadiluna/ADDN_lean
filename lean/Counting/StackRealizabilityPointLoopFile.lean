import Counting.StackRealizabilityPointItem
import Counting.StackRealizabilityPointValues

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def pointLoopData (data : Fin 18→List Bool) (index leaving deficit counter : List Bool) : Fin 18→List Bool :=
  Function.update (Function.update (Function.update (Function.update data 0 index) 4 leaving) 5 deficit) 12 counter

def pointLoopStore (nodes : List Executable.Node) (values : List Nat) (target old : Nat)
    (status : List Bool) (data : Fin 18→List Bool) (index leaving deficit counter : List Bool) : Store 58 :=
  pointFile (massFile ((Encoding.list Encoding.node).encode nodes) ((Encoding.list Encoding.natural).encode values)
    target.bits [] old.bits status [] [] []) (pointLoopData data index leaving deficit counter)

theorem pointLoopStore_counter (nodes : List Executable.Node) (values : List Nat) (target old : Nat)
    (status : List Bool) (data : Fin 18→List Bool) (index leaving deficit counter next : List Bool) :
    Function.update (pointLoopStore nodes values target old status data index leaving deficit counter) 54 next=
      pointLoopStore nodes values target old status data index leaving deficit next := by
  change Function.update (pointFile _ _) (pointExtraRoles 12) next=_
  rw [pointFile_update_data]
  simp only [pointLoopStore,pointLoopData,Function.update_idem]

theorem pointLoopItem_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (target old order visible : Nat) (accepted : Bool) (tail : List Bool)
    (data : Fin 18→List Bool) (index leaving deficit counter : List Bool) (indexAt : index.length=old)
    (e1 : data 1=[]) (hn : data 2=order.bits) (hv : data 3=visible.bits) (e8 : data 8=[]) :
    ∃ time ≤ 200000100*(massInputSize nodes values+target.size+old.size+order.size+visible.size+
      (data 10).length+index.length+1)^15,
      Executes pointItem (pointLoopStore nodes values target old (accepted::tail) data index leaving deficit counter) time
        (pointLoopStore nodes values target (old+1)
          ((accepted && (if RealizabilityVerifier.BitGraph.bitAt (data 10) old then
            roundBoundsCheck (childRangeSum nodes target old 0 values) (values[old]?.getD 0)
              (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values) visible order
            else true))::tail) data (true::index)
          (decide (0<values[old]?.getD 0-childRangeSum nodes target old 0 values)::leaving)
          (decide (demandRangeSum nodes target old 0 values<supplyRangeSum nodes target old 0 values)::deficit) counter) := by
  let localData := pointLoopData data index leaving deficit counter
  obtain ⟨time,bound,run⟩ := pointItem_executes nodes values length sorted target old order visible accepted tail
    localData (by simp [localData,pointLoopData,indexAt]) (by simp [localData,pointLoopData,e1])
    (by simp [localData,pointLoopData,hn]) (by simp [localData,pointLoopData,hv])
    (by simp [localData,pointLoopData,e8])
  have final : pointNextData localData (childRangeSum nodes target old 0 values)
      (values[old]?.getD 0) (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values)=
      pointLoopData data (true::index)
        (decide (0<values[old]?.getD 0-childRangeSum nodes target old 0 values)::leaving)
        (decide (demandRangeSum nodes target old 0 values<supplyRangeSum nodes target old 0 values)::deficit) counter := by
    funext r
    fin_cases r <;> simp [pointNextData,pointResultData,localData,pointLoopData,e1]
  rw [final] at run
  refine ⟨time,?_,?_⟩
  · simpa [pointBodySize,localData,pointLoopData] using bound
  · simpa only [pointLoopStore,localData,pointLoopData,Function.update_of_ne (by decide : (10:Fin 18)≠12),
      Function.update_of_ne (by decide : (10:Fin 18)≠5),Function.update_of_ne (by decide : (10:Fin 18)≠4),
      Function.update_of_ne (by decide : (10:Fin 18)≠0)] using run

end Counting.StackMachine.RealizabilityCheck
