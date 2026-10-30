import Counting.StackProtocolAuditSelected

namespace Counting.StackMachine.ProtocolAudit
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev completeRaw : Routine 70 := sequence prepareInput (sequence schedulerCall afterSchedule)

def rawBudget (vista : Executable.Vista) (leaders round : Nat) : Nat :=
  40*((inputWord vista leaders round).length+1)+4000*((ProtocolSchedule.inputWord leaders round).length+1)+
    afterScheduleBudget vista leaders (Executable.candidateAt leaders round)+2

theorem completeRaw_executes (vista : Executable.Vista) (leaders round : Nat) :
    ∃ time output,time≤ rawBudget vista leaders round ∧
      Executes completeRaw (inputStore 70 (inputWord vista leaders round)) time output ∧
      output 1=outputWord (answer vista leaders round) := by
  obtain ⟨a,abound,arun⟩:=prepareInput_executes vista leaders round
  obtain ⟨b,bbound,brun⟩:=ProtocolSchedule.complete_executes leaders round
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders round 0 0) _ brun
  obtain ⟨c,output,cbound,crun,result⟩:=afterSchedule_executes vista leaders round
    (Executable.candidateAt leaders round)
  exact ⟨_,output,by dsimp only [rawBudget];omega,arun.sequence (lifted.sequence crun),result⟩

abbrev complete : Routine 70 := isolate completeRaw

def completeBudget (vista : Executable.Vista) (leaders round : Nat) : Nat :=
  73*(rawBudget vista leaders round+(inputWord vista leaders round).length+3)

/-- A concrete program chooses the next candidate, runs the full five-step
mathematical audit, emits the counting decision, and clears all work registers. -/
theorem complete_executes (vista : Executable.Vista) (leaders round : Nat) :
    ∃ time≤ completeBudget vista leaders round,
      Executes complete (inputStore 70 (inputWord vista leaders round)) time
        (outputStore 70 (outputWord (answer vista leaders round))) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista leaders round
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ rawBudget vista leaders round ∧
      HaltsAt completeRaw.program (inputWord vista leaders round) time last ∧
      last.store 1=outputWord (answer vista leaders round) :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  obtain ⟨time,bounded,run⟩:=isolate_halts completeRaw (inputWord vista leaders round)
    (outputWord (answer vista leaders round)) _ rawHalt
  exact ⟨time,bounded,run⟩

end Counting.StackMachine.ProtocolAudit
