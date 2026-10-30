import Counting.StackRealizabilityArcValues

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Emit one row-major adjacency bit and advance both matrix addresses.
The incoming address advances by the width because its indices are reversed. -/
def arcItem : Routine 30:=sequence arcPoint
  (sequence (pushBit 9 true)
    (sequence (pushBit 10 true) (ofProgram (ListPrograms.copyProgram 29 29 11 26))))

def arcItemStore (store : Store 30) : Store 30:=
  Function.update (Function.update (Function.update (Function.update store 24 (arcPointValue store::store 24))
    9 (true::store 9)) 10 (true::store 10)) 11 (store 29++store 11)

theorem arcItem_executes (store : Store 30)
    (flags : ∀r : Fin 32,12≤r.val → r.val<24 → store r=[])
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 1100*(arcReadSize store+(store 29).length),
      Executes arcItem store time (arcItemStore store):=by
  obtain ⟨pointTime,pointBound,pointRun⟩:=arcPoint_executes store flags e26 e27 e28
  let emitted:=Function.update store 24 (arcPointValue store::store 24)
  have nextY:=pushBit_executes (9:Fin 32) true emitted
  have yAt : emitted 9=store 9:=by simp [emitted]
  rw [yAt] at nextY
  let steppedY:=Function.update emitted 9 (true::store 9)
  have nextXY:=pushBit_executes (10:Fin 32) true steppedY
  have xyAt : steppedY 10=store 10:=by simp [steppedY,emitted]
  rw [xyAt] at nextXY
  let steppedXY:=Function.update steppedY 10 (true::store 10)
  have copyWidth:=copy_executes 29 29 11 26 (by decide) (by decide) (by decide) steppedXY
    (by simp [steppedXY,steppedY,emitted,e26])
  have widthAt : steppedXY 29=store 29:=by simp [steppedXY,steppedY,emitted]
  have yxAt : steppedXY 11=store 11:=by simp [steppedXY,steppedY,emitted]
  rw [widthAt,yxAt] at copyWidth
  have positive : 1≤arcReadSize store:=by unfold arcReadSize;omega
  exact ⟨_,by omega,pointRun.sequence (nextY.sequence (nextXY.sequence copyWidth))⟩

end Counting.StackMachine.RealizabilityCheck
