import Counting.StackAuditCompleteDispatch

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev completeRaw : Routine 62 := sequence prepareInput (sequence prefixCall afterPrefix)

def rawBudget (vista : Executable.Vista) (leaders candidate last : Nat) : Nat :=
  51*((AuditPrefix.inputWord vista leaders candidate last).length+1)+
  AuditPrefix.completeCoefficient*((AuditPrefix.inputWord vista leaders candidate last).length+1)^7+
  afterPrefixBudget vista leaders candidate last (Executable.auditPrefix? vista leaders candidate last)+2

/-- One concrete stack program implements the entire five-step audit on
binary input. Its correctness theorem has no validity or size assumptions. -/
theorem completeRaw_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time output,time≤ rawBudget vista leaders candidate last ∧
      Executes completeRaw (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) time output ∧
      output 1=witnessWord (Executable.audit? vista leaders candidate last) := by
  obtain ⟨a,abound,arun⟩:=prepareInput_executes vista leaders candidate last
  obtain ⟨b,bbound,brun⟩:=prefixCall_executes vista leaders candidate last
    (metadata vista leaders candidate last [] [])
  obtain ⟨c,cbound,crun⟩:=afterPrefix_executes vista leaders candidate last
    (Executable.auditPrefix? vista leaders candidate last) rfl
  refine ⟨_,_,by dsimp only [rawBudget];omega,arun.sequence (brun.sequence crun),?_⟩
  have answer : answerAfterPrefix vista leaders candidate last (Executable.auditPrefix? vista leaders candidate last)=
      Executable.audit? vista leaders candidate last := by
    rw [audit_eq]
    cases Executable.auditPrefix? vista leaders candidate last <;> rfl
  simpa [file] using congrArg witnessWord answer

abbrev complete : Routine 62 := isolate completeRaw

def completeBudget (vista : Executable.Vista) (leaders candidate last : Nat) : Nat :=
  65*rawBudget vista leaders candidate last+64*(AuditPrefix.inputWord vista leaders candidate last).length+129

theorem complete_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time≤ completeBudget vista leaders candidate last,
      Executes complete (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) time
        (outputStore 62 (witnessWord (Executable.audit? vista leaders candidate last))) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista leaders candidate last
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have ran' : Machine.run (step completeRaw.program) rawTime
      (initial completeRaw.program (AuditPrefix.inputWord vista leaders candidate last))=some finish := ran
  have growth:=run_dataLength (initial completeRaw.program (AuditPrefix.inputWord vista leaders candidate last))
    finish rawTime ran'
  rw [initial_dataLength] at growth
  have registerBound (r:Fin 64) :
      (rawOutput r).length≤ (AuditPrefix.inputWord vista leaders candidate last).length+rawTime := by
    rw [←stored]
    have part : (finish.store r).length≤ finish.dataLength :=
      Finset.single_le_sum (f:=fun i=>(finish.store i).length)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ r)
    exact part.trans growth
  obtain ⟨clearTime,clearBound,clean⟩:=clearRegisters_executes (workRegisters 62) rawOutput
    ((AuditPrefix.inputWord vista leaders candidate last).length+rawTime) registerBound
  have final : clearedStore (workRegisters 62) rawOutput=
      outputStore 62 (witnessWord (Executable.audit? vista leaders candidate last)) := by
    funext r
    by_cases output:r=1
    · subst r;simpa [clearedStore,workRegisters,outputStore] using result
    · simp [clearedStore,workRegisters,outputStore,output]
  rw [final] at clean
  have raw : Executes completeRaw (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) rawTime rawOutput :=
    ⟨finish,ran,halted,stored⟩
  refine ⟨_,?_,raw.sequence clean⟩
  have workCount : (workRegisters 62).length≤ 64 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  have cleanup:=clearBound.trans
    (Nat.mul_le_mul_right ((AuditPrefix.inputWord vista leaders candidate last).length+rawTime+2) workCount)
  dsimp only [completeBudget]
  omega

theorem complete_halts (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time finish,time≤ completeBudget vista leaders candidate last ∧
      HaltsAt complete.program (AuditPrefix.inputWord vista leaders candidate last) time finish ∧
      finish.store 1=witnessWord (Executable.audit? vista leaders candidate last) := by
  obtain ⟨time,bound,finish,ran,halted,stored⟩:=complete_executes vista leaders candidate last
  exact ⟨time,finish,bound,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditComplete
