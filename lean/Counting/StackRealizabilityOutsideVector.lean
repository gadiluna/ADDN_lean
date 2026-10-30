import Counting.StackRealizabilityRepeatBit
import Counting.StackRealizabilityMassFlags
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def outsideCompareRoles : Fin 6 ↪ Fin 9 := ⟨![0,1,5,6,7,8],by decide⟩

def outsideVector : Routine 7 := sequence (differencePositive 3 outsideCompareRoles)
  (sequence (branchRoutine 5 (pushBit 3 true) (pushBit 3 false))
    (sequence (ofProgram (ListPrograms.copyProgram 6 2 4 6))
      (sequence (discardBit 4) (forEach 4 (pushBit 3 false)))))

/-- The last slot is the outside vertex; the preceding slots are inactive.
The width is scanned as an explicit list, never obtained by expanding N. -/
theorem outsideVector_executes (store : Store 7) (order visible : Nat)
    (hn : store 0=order.bits) (hv : store 1=visible.bits)
    (e4 : store 4=[]) (e6 : store 6=[]) (e7 : store 7=[]) (e8 : store 8=[]) :
    ∃ time ≤ 40*(order.size+visible.size+(store 2).length+1),
      Executes outsideVector store time
        (Function.update store 3 (List.replicate ((store 2).length-1) false++
          decide (0<order-visible)::store 3)) := by
  let hidden := decide (0<order-visible)
  have comparing := differencePositive_executes 3 outsideCompareRoles store order visible hn hv e6 e7 e8
  let checked := Function.update store 5 (hidden::store 5)
  have pushing : Executes (branchRoutine 5 (pushBit 3 true) (pushBit 3 false)) checked 2
      (Function.update store 3 (hidden::store 3)) := by
    cases value : hidden with
    | false =>
      have run := branch_executes_false (5:Fin 9) (pushBit 3 true) (pushBit 3 false)
        checked (Function.update store 3 (false::store 3)) (store 5) 1
        (by simp [checked,value]) (by simpa [checked,value] using pushBit_executes (3:Fin 9) false store)
      simpa [value] using run
    | true =>
      have run := branch_executes_true (5:Fin 9) (pushBit 3 true) (pushBit 3 false)
        checked (Function.update store 3 (true::store 3)) (store 5) 1
        (by simp [checked,value]) (by simpa [checked,value] using pushBit_executes (3:Fin 9) true store)
      simpa [value] using run
  let selected := Function.update store 3 (hidden::store 3)
  have copying := copy_executes 6 2 4 6 (by decide) (by decide) (by decide) selected
    (by simp [selected,e6])
  have sourceAt : selected 2=store 2 := by simp [selected]
  have counterAt : selected 4=[] := by simp [selected,e4]
  rw [sourceAt,counterAt,List.append_nil] at copying
  let copied := Function.update selected 4 (store 2)
  have discarding := discardBit_executes (4:Fin 9) copied
  have copiedAt : copied 4=store 2 := by simp [copied]
  rw [copiedAt] at discarding
  let ready := Function.update copied 4 (store 2).tail
  have repeating := repeatPushBit_executes (4:Fin 9) 3 (by decide) false ready (store 2).tail (by simp [ready])
  have readyOutput : ready 3=hidden::store 3 := by simp [ready,copied,selected]
  rw [readyOutput,List.length_tail] at repeating
  have final : Function.update (Function.update ready 4 []) 3
      (List.replicate ((store 2).length-1) false++hidden::store 3)=
      Function.update store 3 (List.replicate ((store 2).length-1) false++hidden::store 3) := by
    simp [ready,copied,selected,e4,Function.update_comm (by decide : (4:Fin 9)≠3)]
  rw [final] at repeating
  have compareBound := Binary.preservingCompareCost_le order.bits visible.bits
  simp only [Encoding.bits_length] at compareBound
  have execution := comparing.sequence (pushing.sequence (copying.sequence (discarding.sequence repeating)))
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
