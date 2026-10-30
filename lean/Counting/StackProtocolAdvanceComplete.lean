import Counting.StackProtocolAdvanceControl
import Counting.StackRoutineIsolateHalt

namespace Counting.StackMachine.ProtocolAdvance
open Routine Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

@[noinline] def completeRaw (core : Bool) : Routine 254 := sequence parseInput (dispatch core)

def rawBudget (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) (updated : Vista) : Nat :=
  20*((inputWord state messages degree).length+1)+60*((stateWord state).length+1)+
    activeBudget core state.leaders state.vista updated messages degree+10

theorem completeRaw_executes (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat)
    (updated : Vista) (valid:state.vista.valid=true)
    (received:∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level)
    (success:updateVista? state.vista messages degree=some updated) :
    ∃time output,time≤ rawBudget core state messages degree updated ∧
      Executes (completeRaw core) (inputStore 254 (inputWord state messages degree)) time output ∧
      output 1=outputWord (transition core state messages degree) := by
  unfold completeRaw
  obtain ⟨a,ab,ar⟩:=parseInput_executes state messages degree
  obtain ⟨b,output,bb,br,value⟩:=dispatch_executes core state messages degree updated valid received success
  exact ⟨_,output,by dsimp only [rawBudget];omega,ar.sequence br,value⟩

@[noinline] def complete (core : Bool) : Routine 254 := isolate (completeRaw core)

def completeBudget (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat) (updated : Vista) : Nat :=
  257*(rawBudget core state messages degree updated+(inputWord state messages degree).length+3)

/-- The original local transition including prior silent halting, the known
leader guard, the complete canonical DAG updater, the selected audit schedule,
state serialization, and erasure of every private work register. -/
theorem complete_executes (core : Bool) (state : LocalState) (messages : List (Vista×Nat)) (degree : Nat)
    (updated : Vista) (valid:state.vista.valid=true)
    (received:∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(state.vista.node state.vista.bottom).level)
    (success:updateVista? state.vista messages degree=some updated) :
    ∃time≤ completeBudget core state messages degree updated,
      Executes (complete core) (inputStore 254 (inputWord state messages degree)) time
        (outputStore 254 (outputWord (transition core state messages degree))) := by
  unfold complete
  obtain ⟨steps,output,bounded,run,result⟩:=completeRaw_executes core state messages degree updated valid received success
  obtain ⟨last,ran,halted,stored⟩:=run
  have halts:∃time last,time≤ rawBudget core state messages degree updated ∧
      HaltsAt (completeRaw core).program (inputWord state messages degree) time last ∧
      last.store 1=outputWord (transition core state messages degree) :=
    ⟨steps,last,bounded,⟨ran,halted⟩,by rw [stored];exact result⟩
  exact isolate_halts (completeRaw core) (inputWord state messages degree)
    (outputWord (transition core state messages degree)) _ halts

end Counting.StackMachine.ProtocolAdvance
