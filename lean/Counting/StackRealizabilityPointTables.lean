import Counting.StackRealizabilityPointTablesFinish

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

def pointTables : Routine 58 := sequence (ofProgram (ListPrograms.copyProgram 57 53 54 0))
  (sequence pointLoop pointTablesFinish)

def pointTablesSize (nodes : List Executable.Node) (values : List Nat)
    (target order visible : Nat) (data : Fin 18→List Bool) : Nat :=
  massInputSize nodes values+target.size+order.size+visible.size+(data 10).length+2*(data 11).length+2

/-- The width comes from an explicit stored counter. Every query is computed
and charged; the two output tables are in increasing slot order. -/
theorem pointTables_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (target order visible : Nat) (accepted : Bool) (tail : List Bool)
    (data : Fin 18→List Bool)
    (e1 : data 1=[]) (hn : data 2=order.bits) (hv : data 3=visible.bits)
    (e6 : data 6=[]) (e7 : data 7=[]) (e8 : data 8=[]) :
    ∃ time ≤ 300000000*(pointTablesSize nodes values target order visible data)^16,
      Executes pointTables
        (pointLoopStore nodes values target 0 (accepted::tail) data [] [] [] []) time
        (pointLoopStore nodes values target 0
          ((accepted && pointRangeCheck nodes values (data 10) target order visible 0 (data 11).length)::tail)
          (Function.update (Function.update data 6 (leavingRangeValues nodes values target 0 (data 11).length))
            7 (deficitRangeValues nodes values target 0 (data 11).length)) [] [] [] []) := by
  let start := pointLoopStore nodes values target 0 (accepted::tail) data [] [] [] []
  have copying := copy_executes 57 53 54 0 (by decide) (by decide) (by decide) start
    (by simp [start,pointLoopStore,pointFile,massFile])
  have at53 : start 53=data 11 := by simp [start,pointLoopStore,pointFile,pointLoopData]
  have at54 : start 54=[] := by simp [start,pointLoopStore,pointFile,pointLoopData]
  rw [at53,at54,List.append_nil] at copying
  have prepared : Function.update start 54 (data 11)=
      pointLoopStore nodes values target 0 (accepted::tail) data [] [] [] (data 11) :=
    pointLoopStore_counter _ _ _ _ _ _ _ _ _ _ _
  rw [prepared] at copying
  obtain ⟨loopTime,loopBound,loopRun⟩ := pointLoop_executes nodes values length sorted target order visible
    tail data e1 hn hv e8 (data 11) 0 accepted [] [] [] rfl
  simp only [Nat.zero_add,List.append_nil] at loopRun loopBound
  obtain ⟨finishTime,finishBound,finishRun⟩ := pointTablesFinish_executes nodes values target (data 11).length
    ((accepted && pointRangeCheck nodes values (data 10) target order visible 0 (data 11).length)::tail)
    data (List.replicate (data 11).length true)
    (leavingRangeValues nodes values target 0 (data 11).length)
    (deficitRangeValues nodes values target 0 (data 11).length) e6 e7
  simp only [leavingRangeValues_length,deficitRangeValues_length,List.length_replicate] at finishBound
  let S := pointTablesSize nodes values target order visible data
  have positive : 1 ≤ S := by dsimp only [S,pointTablesSize];omega
  have widthSmall : (data 11).length ≤ S := by dsimp only [S,pointTablesSize];omega
  have widthBits : ((data 11).length).size ≤ (data 11).length := Nat.size_le.mpr Nat.lt_two_pow_self
  have linear : S ≤ S^16 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^16 := Nat.one_le_pow _ _ positive
  change loopTime ≤ (data 11).length*(200000100*S^15+2)+1 at loopBound
  have product : (data 11).length*(200000100*S^15+2) ≤ 200000100*S^16+2*S := by
    calc _ ≤ S*(200000100*S^15+2) := Nat.mul_le_mul_right _ widthSmall
         _ = _ := by ring
  have execution := copying.sequence (loopRun.sequence finishRun)
  exact ⟨_,by change _ ≤ 300000000*S^16;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
