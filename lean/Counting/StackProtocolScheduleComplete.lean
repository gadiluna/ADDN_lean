import Counting.StackProtocolScheduleControl
import Counting.StackRoutineIsolateHalt

namespace Counting.StackMachine.ProtocolSchedule
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev completeRaw : Routine 14 := sequence parse body

theorem completeRaw_executes (leaders round : Nat) :
    ∃ time output,time≤ 210*(leaders.size+round.size+1) ∧
      Executes completeRaw (inputStore 14 (inputWord leaders round)) time output ∧
      output 1=outputWord (Executable.candidateAt leaders round) := by
  have a:=parse_executes leaders round
  obtain ⟨b,output,bbound,brun,result⟩:=body_executes leaders round
  exact ⟨_,_,by omega,a.sequence brun,result⟩

abbrev complete : Routine 14 := isolate completeRaw

/-- Complete binary candidate scheduler, including input parsing and cleanup.
The bound is uniform in the bit lengths of arbitrarily large round labels. -/
theorem complete_executes (leaders round : Nat) :
    ∃ time≤ 4000*((inputWord leaders round).length+1),
      Executes complete (inputStore 14 (inputWord leaders round)) time
        (outputStore 14 (outputWord (Executable.candidateAt leaders round))) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes leaders round
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ 210*(leaders.size+round.size+1) ∧
      HaltsAt completeRaw.program (inputWord leaders round) time last ∧
      last.store 1=outputWord (Executable.candidateAt leaders round) :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  obtain ⟨time,bounded,run⟩:=isolate_halts completeRaw (inputWord leaders round)
    (outputWord (Executable.candidateAt leaders round)) _ rawHalt
  refine ⟨time,bounded.trans ?_,run⟩
  simp only [inputWord,List.length_append,Encoding.natural_length]
  omega

theorem complete_halts (leaders round : Nat) :
    ∃ time finish,time≤ 4000*((inputWord leaders round).length+1) ∧
      HaltsAt complete.program (inputWord leaders round) time finish ∧
      finish.store 1=outputWord (Executable.candidateAt leaders round) := by
  obtain ⟨time,bound,finish,ran,halted,stored⟩:=complete_executes leaders round
  exact ⟨time,finish,bound,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.ProtocolSchedule
