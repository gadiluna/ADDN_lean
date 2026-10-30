import Counting.StackAuditPrefixSaveConditional
import Counting.StackEncodingFrameStore
import Counting.AuditPrefixScanState

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

abbrev emitAnchor : Routine 50 := branchRoutine 1
  (frameRoutine 49 46 1 51) (sequence (clear 46) (pushBit 1 false))

/-- Encode the accepted optional anchor, or the canonical `none` on failure.
The branch consumes the status and the saved binary anchor is always erased. -/
theorem emitAnchor_executes (store : Store 50) (accepted : Bool) (anchor : Option Nat)
    (status : store 1=[accepted]) (saved : store 46=(anchorCode anchor).bits)
    (empty : store 51=[]) :
    ∃ time ≤ 5*(anchorCode anchor).size+5,
      Executes emitAnchor store time
        (Function.update (Function.update store 46 []) 1
          (Encoding.optionalNatural.encode (if accepted then anchor else none))) := by
  let consumed:=Function.update store 1 []
  cases accepted with
  | false=>
    have a:=clear_executes (46:Fin 52) consumed
    have source : consumed 46=(anchorCode anchor).bits := by simp [consumed,saved]
    rw [source,Encoding.bits_length] at a
    let erased:=Function.update consumed 46 []
    have b:=pushBit_executes (1:Fin 52) false erased
    have output : erased 1=[] := by simp [erased,consumed]
    rw [output] at b
    have branch:=branch_executes_false (1:Fin 52) (frameRoutine 49 46 1 51)
      (sequence (clear 46) (pushBit 1 false)) store _ [] _ status (a.sequence b)
    have final : Function.update erased 1 [false]=
        Function.update (Function.update store 46 []) 1 (Encoding.optionalNatural.encode none) := by
      funext r
      by_cases r1:r=1 <;> by_cases r46:r=46 <;>
        simp [erased,consumed,r1,r46,Encoding.optionalNatural,Encoding.transport,
          Encoding.natural,Encoding.frame,Nat.bits]
    rw [final] at branch
    exact ⟨_,by omega,branch⟩
  | true=>
    have a:=frame_executes_updates 49 (46:Fin 52) 1 51
      (by decide) (by decide) (by decide) consumed (by simp [consumed,empty])
    have source : consumed 46=(anchorCode anchor).bits := by simp [consumed,saved]
    have target : consumed 1=[] := by simp [consumed]
    rw [source,target,List.append_nil,Encoding.bits_length] at a
    have branch:=branch_executes_true (1:Fin 52) (frameRoutine 49 46 1 51)
      (sequence (clear 46) (pushBit 1 false)) store _ [] _ status a
    have final : Function.update (Function.update consumed 46 []) 1
        (Encoding.frame (anchorCode anchor).bits)=
        Function.update (Function.update store 46 []) 1 (Encoding.optionalNatural.encode anchor) := by
      funext r
      by_cases r1:r=1 <;> by_cases r46:r=46 <;>
        simp [consumed,r1,r46,Encoding.optionalNatural,Encoding.transport,Encoding.natural,anchorCode]
    rw [final] at branch
    exact ⟨_,by omega,branch⟩

end Counting.StackMachine.AuditPrefix
