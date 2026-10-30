import Counting.StackAuditPrefixCompleteGuard
import Counting.StackRoutineClean

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev complete : Routine 50 := isolate completeRaw

def completeCoefficient : Nat := 3300000000000

/-- The complete prefix computation includes charged erasure of every
working register. Its sole output is the canonical optional-anchor code;
no validity, depth, population, or successful-anchor premise is assumed. -/
theorem complete_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time ≤ completeCoefficient*((inputWord vista leaders candidate last).length+1)^7,
      Executes complete (inputStore 50 (inputWord vista leaders candidate last)) time
        (outputStore 50 (Encoding.optionalNatural.encode
          (Executable.auditPrefix? vista leaders candidate last))) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista leaders candidate last
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have ran' : Machine.run (step completeRaw.program) rawTime
      (initial completeRaw.program (inputWord vista leaders candidate last))=some finish := ran
  have growth:=run_dataLength (initial completeRaw.program (inputWord vista leaders candidate last))
    finish rawTime ran'
  rw [initial_dataLength] at growth
  have registerBound (r : Fin 52) :
      (rawOutput r).length≤(inputWord vista leaders candidate last).length+rawTime := by
    rw [←stored]
    have part : (finish.store r).length≤finish.dataLength :=
      Finset.single_le_sum (f:=fun i=>(finish.store i).length)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ r)
    exact part.trans growth
  obtain ⟨clearTime,clearBound,clean⟩:=clearRegisters_executes (workRegisters 50)
    rawOutput ((inputWord vista leaders candidate last).length+rawTime) registerBound
  have final : clearedStore (workRegisters 50) rawOutput=
      outputStore 50 (Encoding.optionalNatural.encode (Executable.auditPrefix? vista leaders candidate last)) := by
    funext r
    by_cases output:r=1
    · subst r
      simpa [clearedStore,workRegisters,outputStore] using result
    · simp [clearedStore,workRegisters,outputStore,output]
  rw [final] at clean
  have raw : Executes completeRaw (inputStore 50 (inputWord vista leaders candidate last)) rawTime rawOutput :=
    ⟨finish,ran,halted,stored⟩
  refine ⟨_,?_,raw.sequence clean⟩
  have workCount : (workRegisters 50).length≤52 := by
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have cleanup:=clearBound.trans
    (Nat.mul_le_mul_right ((inputWord vista leaders candidate last).length+rawTime+2) workCount)
  let L:=(inputWord vista leaders candidate last).length+1
  have linear : L≤L^7:=Nat.le_self_pow (by decide) _
  have one : 1≤L^7:=Nat.one_le_pow _ _ (by dsimp only [L];omega)
  change rawTime≤61000000000*L^7 at rawBound
  change rawTime+1+clearTime≤3300000000000*L^7
  dsimp only [L] at linear one rawBound ⊢
  omega

theorem complete_halts (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time finish,time≤completeCoefficient*((inputWord vista leaders candidate last).length+1)^7 ∧
      HaltsAt complete.program (inputWord vista leaders candidate last) time finish ∧
      finish.store 1=Encoding.optionalNatural.encode (Executable.auditPrefix? vista leaders candidate last) := by
  obtain ⟨time,bound,finish,ran,halted,stored⟩:=complete_executes vista leaders candidate last
  exact ⟨time,finish,bound,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditPrefix
