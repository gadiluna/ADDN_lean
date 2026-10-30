import Counting.StackProtocolDecisionControl

namespace Counting.StackMachine.ProtocolDecision
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev completeRaw : Routine 78 := sequence prepareInput (sequence vistaCall (sequence readSummary control))

def rawBudget (vista : Executable.Vista) (leaders : Nat) : Nat :=
  20*((inputWord vista leaders).length+1)+3000000*((Encoding.vista.encode vista).length+1)^5+
    20*((ProtocolVista.outputWord vista).length+1)+normalBudget vista leaders (vista.node vista.bottom).level+
    40*(leaders.size+(vista.node vista.bottom).level.size+1)+13

theorem completeRaw_executes (vista : Executable.Vista) (leaders : Nat) (valid : vista.valid=true) :
    ∃ time output,time≤ rawBudget vista leaders ∧
      Executes completeRaw (inputStore 78 (inputWord vista leaders)) time output ∧
      output 1=outputWord (Executable.scheduledPlan leaders vista).eval := by
  obtain ⟨a,abound,arun⟩:=prepareInput_executes vista leaders
  obtain ⟨b,bbound,brun⟩:=ProtocolVista.complete_executes vista valid
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders 0 []) _ brun
  obtain ⟨c,cbound,crun⟩:=readSummary_executes vista leaders
  obtain ⟨d,output,dbound,drun,result⟩:=control_executes vista leaders (vista.node vista.bottom).level
    (ProtocolVista.allRootLeaders vista)
  rw [decision_eq_scheduledPlan] at result
  exact ⟨_,output,by dsimp only [rawBudget];omega,arun.sequence (lifted.sequence (crun.sequence drun)),result⟩

abbrev complete : Routine 78 := isolate completeRaw

def completeBudget (vista : Executable.Vista) (leaders : Nat) : Nat :=
  81*(rawBudget vista leaders+(inputWord vista leaders).length+3)

/-- The complete original scheduled solver plan is executed from precisely
its local parameters: leader count and the serialized vista. No global
population, supplied round, or supplied all-leader predicate is available. -/
theorem complete_executes (vista : Executable.Vista) (leaders : Nat) (valid : vista.valid=true) :
    ∃ time≤ completeBudget vista leaders,
      Executes complete (inputStore 78 (inputWord vista leaders)) time
        (outputStore 78 (outputWord (Executable.scheduledPlan leaders vista).eval)) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista leaders valid
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ rawBudget vista leaders ∧
      HaltsAt completeRaw.program (inputWord vista leaders) time last ∧
      last.store 1=outputWord (Executable.scheduledPlan leaders vista).eval :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  exact isolate_halts completeRaw (inputWord vista leaders)
    (outputWord (Executable.scheduledPlan leaders vista).eval) _ rawHalt

end Counting.StackMachine.ProtocolDecision
