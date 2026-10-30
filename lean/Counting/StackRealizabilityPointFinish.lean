import Counting.StackRealizabilityPointFile
import Counting.StackRealizabilityPointNumeric
import Counting.StackRealizabilityBitLookup

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def pointOldRoles : Fin 7 ↪ Fin 60 := ⟨![52,42,50,49,0,2,3],by decide⟩
def pointOld : Routine 58 := bitLookup 53 pointOldRoles

def pointCleanup : Routine 58 := sequence (clear 21)
  (sequence (clear 26) (sequence (clear 37) (sequence (clear 43) (clear 50))))

theorem pointCleanup_executes (store : Store 58) :
    Executes pointCleanup store
      ((store 21).length+(store 26).length+(store 37).length+(store 43).length+(store 50).length+9)
      (Function.update (Function.update (Function.update (Function.update (Function.update store
        21 []) 26 []) 37 []) 43 []) 50 []) := by
  have a := clear_executes (21:Fin 60) store
  have b := clear_executes (26:Fin 60) (Function.update store 21 [])
  have c := clear_executes (37:Fin 60) (Function.update (Function.update store 21 []) 26 [])
  have d := clear_executes (43:Fin 60) (Function.update (Function.update (Function.update store 21 []) 26 []) 37 [])
  have e := clear_executes (50:Fin 60) (Function.update (Function.update (Function.update (Function.update store 21 []) 26 []) 37 []) 43 [])
  have run := a.sequence (b.sequence (c.sequence (d.sequence e)))
  convert run using 1 <;> simp [pointCleanup]
  omega

def pointFinish : Routine 58 := sequence pointOld (sequence pointNumeric pointCleanup)

def pointResultData (data : Fin 18→List Bool) (child weight supply demand : Nat) : Fin 18→List Bool :=
  Function.update (Function.update (Function.update data 1 []) 4
    (decide (0<weight-child)::data 4)) 5 (decide (demand<supply)::data 5)

theorem pointFinish_executes (source weights level query : List Bool)
    (child weight supply demand visible order : Nat) (accepted : Bool) (tail : List Bool)
    (data : Fin 18→List Bool)
    (hw : data 1=weight.bits) (hn : data 2=order.bits) (hv : data 3=visible.bits)
    (empty : data 8=[]) :
    let active := RealizabilityVerifier.BitGraph.bitAt (data 10) (data 0).length
    ∃ time ≤ 6*(data 10).length+7*(data 0).length+
      240*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1),
      Executes pointFinish
        (pointFile (massFile source weights level [] query (accepted::tail)
          child.bits demand.bits supply.bits) data) time
        (pointFile (massFile source weights level [] query
          ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)
          [] [] []) (pointResultData data child weight supply demand)) := by
  dsimp only
  let active := RealizabilityVerifier.BitGraph.bitAt (data 10) (data 0).length
  let start := pointFile (massFile source weights level [] query (accepted::tail)
    child.bits demand.bits supply.bits) data
  obtain ⟨readTime,readBound,reading⟩ := bitLookup_executes 53 pointOldRoles start
    (by simp [start,pointFile,massFile,pointOldRoles])
    (by simp [start,pointFile,massFile,pointOldRoles])
    (by simp [start,pointFile,massFile,pointOldRoles])
  let ready := Function.update start 50 [active]
  have reading' : Executes pointOld start readTime ready := by
    simpa [pointOld,pointOldRoles,start,pointFile,empty,active] using reading
  have readBound' : readTime ≤ 6*(data 10).length+7*(data 0).length+16 := by
    simpa [start,pointFile,pointOldRoles] using readBound
  obtain ⟨numericTime,numericBound,numericRun⟩ := pointNumeric_executes ready
    child weight supply demand visible order
    (by simp [ready,start,pointFile,massFile]) (by simp [ready,start,pointFile,hw])
    (by simp [ready,start,pointFile,massFile]) (by simp [ready,start,pointFile,massFile])
    (by simp [ready,start,pointFile,hv]) (by simp [ready,start,pointFile,hn])
    accepted active tail [] (by simp [ready,start,pointFile,massFile]) (by simp [ready])
    (by simp [ready,start,pointFile,massFile]) (by simp [ready,start,pointFile,massFile])
    (by simp [ready,start,pointFile,massFile])
  let checked := pointNumericStore ready child weight supply demand visible order accepted active tail
  have cleaning := pointCleanup_executes checked
  have final : Function.update (Function.update (Function.update (Function.update (Function.update checked
      21 []) 26 []) 37 []) 43 []) 50 [] =
      pointFile (massFile source weights level [] query
        ((accepted && (if active then roundBoundsCheck child weight supply demand visible order else true))::tail)
        [] [] []) (pointResultData data child weight supply demand) := by
    funext r
    fin_cases r <;> simp [checked,pointNumericStore,ready,start,pointFile,massFile,pointResultData,empty]
  rw [final] at cleaning
  have cleanupTime : (checked 21).length+(checked 26).length+(checked 37).length+
      (checked 43).length+(checked 50).length+9 = child.size+demand.size+supply.size+weight.size+10 := by
    simp [checked,pointNumericStore,ready,start,pointFile,massFile,hw,Encoding.bits_length]
  rw [cleanupTime] at cleaning
  have execution := reading'.sequence (numericRun.sequence cleaning)
  exact ⟨readTime+1+(numericTime+1+(child.size+demand.size+supply.size+weight.size+10)),by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
