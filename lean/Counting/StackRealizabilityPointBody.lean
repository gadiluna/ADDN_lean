import Counting.StackRealizabilityPointFinish
import Counting.StackRealizabilityMassInputBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def pointBody : Routine 58 := sequence pointCalculate (sequence pointWeight pointFinish)

def pointBodySize (nodes : List Executable.Node) (values : List Nat)
    (target old order visible : Nat) (data : Fin 18→List Bool) : Nat :=
  massInputSize nodes values+target.size+old.size+order.size+visible.size+
    (data 10).length+(data 0).length+1

/-- One actual binary query performs the three scans, the indexed weight read,
the old-level lookup and the guarded numerical checks. Both encoded input
lists, the query, the level, and all unrelated loop cells are preserved. -/
theorem pointBody_executes (nodes : List Executable.Node) (values : List Nat)
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
    ∃ time ≤ 200000000*(pointBodySize nodes values target old order visible data)^15,
      Executes pointBody
        (pointFile (massFile source weights target.bits [] old.bits (accepted::tail) [] [] []) data) time
        (pointFile (massFile source weights target.bits [] old.bits
          ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)
          [] [] []) (pointResultData data child weight supply demand)) := by
  dsimp only
  let source := (Encoding.list Encoding.node).encode nodes
  let weights := (Encoding.list Encoding.natural).encode values
  let child := childRangeSum nodes target old 0 values
  let supply := supplyRangeSum nodes target old 0 values
  let demand := demandRangeSum nodes target old 0 values
  let weight := values[old]?.getD 0
  let active := RealizabilityVerifier.BitGraph.bitAt (data 10) old
  let updated := Function.update data 1 weight.bits
  obtain ⟨massTime,massBound,massRun⟩ := pointCalculate_executes source weights accepted tail
    nodes sorted values length [] [] (by simp [source]) (by simp [weights]) target old data
  obtain ⟨weightTime,weightBound,weightRun⟩ := pointWeight_executes source target.bits [] old.bits
    (accepted::tail) child.bits demand.bits supply.bits values data e1
  rw [indexAt] at weightRun
  obtain ⟨finishTime,finishBound,finishRun⟩ := pointFinish_executes source weights target.bits old.bits
    child weight supply demand visible order accepted tail updated
    (by simp [updated]) (by simp [updated,hn]) (by simp [updated,hv]) (by simp [updated,e8])
  have resultData : pointResultData updated child weight supply demand=
      pointResultData data child weight supply demand := by
    funext r
    fin_cases r <;> simp [pointResultData,updated]
  simp only [updated,Function.update_of_ne (by decide : (10:Fin 18)≠1),
    Function.update_of_ne (by decide : (0:Fin 18)≠1)] at finishRun finishBound
  rw [indexAt,resultData] at finishRun
  let S := pointBodySize nodes values target old order visible data
  have positive : 1 ≤ S := by dsimp only [S,pointBodySize];omega
  have linear : S ≤ S^15 := Nat.le_self_pow (by decide) _
  have square : S^2 ≤ S^15 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  have inputSmall : massInputSize nodes values ≤ S := by dsimp only [S,pointBodySize];omega
  have massSmall : source.length+weights.length+target.size+old.size+2 ≤ S := by
    dsimp only [source,weights,S,pointBodySize,massInputSize]
    omega
  have mainBound := (Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left massSmall 15))
  have sizes := massRangeSums_size nodes values length sorted target old
  have inputSquare : (massInputSize nodes values)^2 ≤ S^2 := Nat.pow_le_pow_left inputSmall 2
  have weightSize := naturalPayload_size_le_sequence values old
  have weightSequence : (Encoding.sequence Encoding.natural values).length ≤ S := by
    have small : (Encoding.sequence Encoding.natural values).length ≤ massInputSize nodes values := by
      change _ ≤ ((Encoding.list Encoding.node).encode nodes).length+
        (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length+1
      simp only [List.length_append]
      omega
    exact small.trans inputSmall
  have context : weights.length+order.size+visible.size+(data 10).length+(data 0).length ≤ S := by
    dsimp only [weights,S,pointBodySize,massInputSize]
    omega
  change massTime ≤ 100000000*(source.length+weights.length+target.size+old.size+2)^15 at massBound
  change weightTime ≤ 10*weights.length+8*(data 0).length+28 at weightBound
  change finishTime ≤ 6*(data 10).length+7*(data 0).length+
    240*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1) at finishBound
  change child.size ≤ 2*(massInputSize nodes values)^2 ∧
    supply.size ≤ 2*(massInputSize nodes values)^2 ∧ demand.size ≤ 2*(massInputSize nodes values)^2 at sizes
  change weight.size ≤ _ at weightSize
  have execution := massRun.sequence (weightRun.sequence finishRun)
  refine ⟨_,?_,execution⟩
  change _ ≤ 200000000*S^15
  omega

end Counting.StackMachine.RealizabilityCheck
