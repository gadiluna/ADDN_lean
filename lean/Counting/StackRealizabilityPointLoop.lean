import Counting.StackRealizabilityPointLoopFile

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

def pointLoop : Routine 58 := forEach 54 pointItem

theorem pointLoop_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (target order visible : Nat) (tail : List Bool) (data : Fin 18→List Bool)
    (e1 : data 1=[]) (hn : data 2=order.bits) (hv : data 3=visible.bits) (e8 : data 8=[])
    (bits : List Bool) (old : Nat) (accepted : Bool) (index leaving deficit : List Bool)
    (indexAt : index.length=old) :
    let S := massInputSize nodes values+target.size+order.size+visible.size+(data 10).length+
      2*(old+bits.length)+2
    ∃ time ≤ bits.length*(200000100*S^15+2)+1,
      Executes pointLoop (pointLoopStore nodes values target old (accepted::tail) data index leaving deficit bits) time
        (pointLoopStore nodes values target (old+bits.length)
          ((accepted && pointRangeCheck nodes values (data 10) target order visible old bits.length)::tail)
          data ((List.replicate bits.length true)++index)
          ((leavingRangeValues nodes values target old bits.length).reverse++leaving)
          ((deficitRangeValues nodes values target old bits.length).reverse++deficit) []) := by
  dsimp only
  induction bits generalizing old accepted index leaving deficit with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (54:Fin 60) pointItem
      (pointLoopStore nodes values target old (accepted::tail) data index leaving deficit [])
      (by simp [pointLoopStore,pointFile,pointLoopData])
    exact ⟨1,by simp,⟨1,_⟩,ran,halted,by simp [pointRangeCheck,leavingRangeValues,deficitRangeValues]⟩
  | cons bit bits ih =>
    let nextAccepted := accepted && (if RealizabilityVerifier.BitGraph.bitAt (data 10) old then
      roundBoundsCheck (childRangeSum nodes target old 0 values) (values[old]?.getD 0)
        (supplyRangeSum nodes target old 0 values) (demandRangeSum nodes target old 0 values) visible order else true)
    let nextLeaving := decide (0<values[old]?.getD 0-childRangeSum nodes target old 0 values)::leaving
    let nextDeficit := decide (demandRangeSum nodes target old 0 values<supplyRangeSum nodes target old 0 values)::deficit
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalted,bodyStore⟩ := pointLoopItem_executes
      nodes values length sorted target old order visible accepted tail data index leaving deficit bits
      indexAt e1 hn hv e8
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalted,tailStore⟩ := ih (old+1) nextAccepted
      (true::index) nextLeaving nextDeficit (by simp [indexAt])
    let original := pointLoopStore nodes values target old (accepted::tail) data index leaving deficit (bit::bits)
    have iteration := repeat_iteration (54:Fin 60) pointItem original bit bits
      (by simp [original,pointLoopStore,pointFile,pointLoopData]) bodyTime bodyFinish
      (by simpa only [original,pointLoopStore_counter] using bodyRun) bodyHalted
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalted,?_⟩
    · let S := massInputSize nodes values+target.size+order.size+visible.size+(data 10).length+
        2*(old+(bit::bits).length)+2
      have oldSize : old.size ≤ old := Nat.size_le.mpr Nat.lt_two_pow_self
      have bodyLimit : bodyTime ≤ 200000100*S^15 := bodyBound.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];simp only [List.length_cons];omega) 15))
      have tailSize : massInputSize nodes values+target.size+order.size+visible.size+(data 10).length+
          2*(old+1+bits.length)+2=S := by dsimp only [S];simp only [List.length_cons];omega
      rw [tailSize] at tailBound
      change bodyTime+2+tailTime ≤ (bit::bits).length*(200000100*S^15+2)+1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · change Machine.run (step pointLoop.program) (bodyTime+2)
        ⟨0,pointLoopStore nodes values target old (accepted::tail) data index leaving deficit (bit::bits)⟩=
          some ⟨0,bodyFinish.store⟩ at iteration
      rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun
    · apply tailStore.trans
      have query : old+1+bits.length=old+(bit::bits).length := by simp only [List.length_cons];omega
      simp only [query]
      congr 1
      · simp [nextAccepted,pointRangeCheck,Bool.and_assoc]
      · simp only [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append]
      · simp [leavingRangeValues,nextLeaving,List.append_assoc]
      · simp [deficitRangeValues,nextDeficit,List.append_assoc]

end Counting.StackMachine.RealizabilityCheck
