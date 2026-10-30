import Counting.StackRealizabilityPointBody
import Counting.StackDagIncrement

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def pointAdvance : Routine 58 := sequence (DagValidation.incrementRoutine 57 0 36 2) (pushBit 42 true)

def pointNextData (data : Fin 18→List Bool) (child weight supply demand : Nat) : Fin 18→List Bool :=
  Function.update (pointResultData data child weight supply demand) 0 (true::data 0)

def pointItem : Routine 58 := sequence pointBody pointAdvance

theorem pointAdvance_executes (source weights level status : List Bool) (old : Nat)
    (data : Fin 18→List Bool) :
    ∃ time ≤ 4*(old.size+1)+5,
      Executes pointAdvance (pointFile (massFile source weights level [] old.bits status [] [] []) data) time
        (pointFile (massFile source weights level [] (old+1).bits status [] [] [])
          (Function.update data 0 (true::data 0))) := by
  let start := pointFile (massFile source weights level [] old.bits status [] [] []) data
  obtain ⟨time,bound,run⟩ := DagValidation.increment_natural 57 0 36 2 (by decide) (by decide) (by decide)
    start (by simp [start,pointFile,massFile]) (by simp [start,pointFile,massFile])
    old (by simp [start,pointFile,massFile])
  have push := pushBit_executes (42:Fin 60) true (Function.update start 36 (old+1).bits)
  have final : Function.update (Function.update start 36 (old+1).bits) 42
      (true::Function.update start 36 (old+1).bits 42)=
      pointFile (massFile source weights level [] (old+1).bits status [] [] [])
        (Function.update data 0 (true::data 0)) := by
    funext r
    fin_cases r <;> simp [start,pointFile,massFile]
  rw [final] at push
  exact ⟨_,by omega,run.sequence push⟩

theorem pointItem_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (target old order visible : Nat) (accepted : Bool) (tail : List Bool)
    (data : Fin 18→List Bool) (indexAt : (data 0).length=old)
    (e1 : data 1=[]) (hn : data 2=order.bits) (hv : data 3=visible.bits) (e8 : data 8=[]) :
    let source := (Encoding.list Encoding.node).encode nodes
    let weights := (Encoding.list Encoding.natural).encode values
    let child := childRangeSum nodes target old 0 values
    let supply := supplyRangeSum nodes target old 0 values
    let demand := demandRangeSum nodes target old 0 values
    let weight := values[old]?.getD 0
    let active := RealizabilityVerifier.BitGraph.bitAt (data 10) old
    ∃ time ≤ 200000100*(pointBodySize nodes values target old order visible data)^15,
      Executes pointItem
        (pointFile (massFile source weights target.bits [] old.bits (accepted::tail) [] [] []) data) time
        (pointFile (massFile source weights target.bits [] (old+1).bits
          ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)
          [] [] []) (pointNextData data child weight supply demand)) := by
  dsimp only
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := pointBody_executes nodes values length sorted target old order visible
    accepted tail data indexAt e1 hn hv e8
  obtain ⟨advanceTime,advanceBound,advanceRun⟩ := pointAdvance_executes
    ((Encoding.list Encoding.node).encode nodes) ((Encoding.list Encoding.natural).encode values)
    target.bits _ old (pointResultData data (childRangeSum nodes target old 0 values)
      (values[old]?.getD 0) (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values))
  have result : Function.update (pointResultData data (childRangeSum nodes target old 0 values)
      (values[old]?.getD 0) (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values))
      0 (true::pointResultData data (childRangeSum nodes target old 0 values)
      (values[old]?.getD 0) (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values) 0)=
      pointNextData data (childRangeSum nodes target old 0 values) (values[old]?.getD 0)
        (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values) := by
    simp [pointNextData,pointResultData]
  rw [result] at advanceRun
  let S := pointBodySize nodes values target old order visible data
  have positive : 1 ≤ S := by dsimp only [S,pointBodySize];omega
  have linear : S ≤ S^15 := Nat.le_self_pow (by decide) _
  have oldSmall : old.size+1 ≤ S := by dsimp only [S,pointBodySize];omega
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  have execution := bodyRun.sequence advanceRun
  exact ⟨_,by change _ ≤ 200000100*S^15;change bodyTime ≤ 200000000*S^15 at bodyBound;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
