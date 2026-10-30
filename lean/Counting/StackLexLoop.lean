import Counting.StackLexStep
import Counting.StackLexStateLemmas

namespace Counting.StackMachine.Lexicographic
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def streamLoop : Routine 14 := forEach 13 streamStep

def loopStore (store : Store 14) (value : LexState) (counter : List Bool) : Store 14 :=
  stateStore (Function.update store 13 counter) value

def streamLoopCost : Nat → LexState → Nat
  | 0,_ => 1
  | count+1,value => streamStepCost value+2+streamLoopCost count value.advance

theorem loopStore_counter (store : Store 14) (value : LexState) (counter : List Bool) :
    loopStore store value counter 13=counter := by simp [loopStore,stateStore]

theorem loopStore_update_counter (store : Store 14) (value : LexState) (before after : List Bool) :
    Function.update (loopStore store value before) 13 after=loopStore store value after := by
  funext r
  fin_cases r <;> simp [loopStore,stateStore]

/-- Every iteration is a physical parser/comparator call. The iteration
count comes from a caller-supplied explicit counter, not from list evaluation. -/
theorem streamLoop_executes (store : Store 14) (value : LexState) (counter : List Bool)
    (empty : ∀ r : Fin 16,r=0 ∨ r=1 ∨ (4≤r.val ∧ r.val≤9) ∨ r=12 → store r=[]) :
    Executes streamLoop (loopStore store value counter) (streamLoopCost counter.length value)
      (loopStore store ((LexState.advance)^[counter.length] value) []) := by
  induction counter generalizing value with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (13:Fin 16) streamStep (loopStore store value [])
      (loopStore_counter store value [])
    exact ⟨⟨1,loopStore store value []⟩,ran,halted,rfl⟩
  | cons bit counter ih =>
    have one := streamStep_executes (Function.update store 13 counter) value (by
      intro r allowed
      fin_cases r <;> simp_all)
    change Executes streamStep (loopStore store value counter) (streamStepCost value)
      (loopStore store value.advance counter) at one
    obtain ⟨middle,bodyRun,bodyHalt,bodyStore⟩ := one
    obtain ⟨finish,tailRun,tailHalt,tailStore⟩ := ih value.advance
    have ran := repeat_iteration (13:Fin 16) streamStep (loopStore store value (bit::counter)) bit counter
      (loopStore_counter store value (bit::counter)) (streamStepCost value) middle
      (by rw [loopStore_update_counter];exact bodyRun) bodyHalt
    change Machine.run (step streamLoop.program) (streamStepCost value+2)
      ⟨0,loopStore store value (bit::counter)⟩=some ⟨0,middle.store⟩ at ran
    refine ⟨finish,?_,tailHalt,?_⟩
    · change Machine.run (step streamLoop.program)
        ((streamStepCost value+2)+streamLoopCost counter.length value.advance) _=some finish
      rw [Machine.run_add,ran,Option.bind_some,bodyStore]
      exact tailRun
    · simpa only [List.length_cons,Function.iterate_succ_apply] using tailStore

theorem streamLoopCost_le (count : Nat) (value : LexState) :
    streamLoopCost count value≤count*(60*(value.encodedLength+1)+2)+1 := by
  induction count generalizing value with
  | zero => simp [streamLoopCost]
  | succ count ih =>
    have body := streamStepCost_le value
    have rest := ih value.advance
    have size := value.advance_encodedLength
    have product := Nat.mul_le_mul_left count (show
      60*(value.advance.encodedLength+1)+2≤60*(value.encodedLength+1)+2 by omega)
    simp only [streamLoopCost]
    nlinarith

end Counting.StackMachine.Lexicographic
