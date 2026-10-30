import Counting.StackProtocolDecisionOutput
import Counting.StackCoreAuditPolynomial
import Counting.StackCoreAuditRefinement

namespace Counting.StackMachine.CoreDecision
open Routine ProtocolDecision
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

abbrev coreAuditCall : Routine 78 := relocate CoreAudit.complete (roles 70 (by decide))
abbrev normal : Routine 78 := sequence normalInput coreAuditCall

def normalBudget (vista : Executable.Vista) (leaders round : Nat) : Nat :=
  30*((ProtocolAudit.inputWord vista leaders round).length+1)+CoreAudit.completeBudget vista leaders round+1

theorem normal_executes (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) :
    ∃ time≤ normalBudget vista leaders round,
      Executes normal (file [] [] (metadata vista leaders round flag)) time
        (file [] (outputWord (CoreAudit.answer vista leaders round)) (metadata vista leaders round flag)) := by
  obtain ⟨a,abound,arun⟩:=normalInput_executes vista leaders round flag
  obtain ⟨b,bbound,brun⟩:=CoreAudit.complete_executes vista leaders round
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders round flag) _ brun
  exact ⟨_,by dsimp only [normalBudget];omega,arun.sequence lifted⟩

abbrev completeRaw : Routine 78 := sequence prepareInput (sequence vistaCall (sequence readSummary normal))

def rawBudget (vista : Executable.Vista) (leaders : Nat) : Nat :=
  20*((inputWord vista leaders).length+1)+3000000*((Encoding.vista.encode vista).length+1)^5+
    20*((ProtocolVista.outputWord vista).length+1)+normalBudget vista leaders (vista.node vista.bottom).level+
    40*(leaders.size+(vista.node vista.bottom).level.size+1)+13

theorem completeRaw_executes (vista : Executable.Vista) (leaders : Nat) (valid : vista.valid=true)
    (positive : 0<leaders) :
    ∃ time output,time≤ rawBudget vista leaders ∧
      Executes completeRaw (inputStore 78 (inputWord vista leaders)) time output ∧
      output 1=outputWord (Executable.coreScheduledPlan leaders vista).eval := by
  obtain ⟨a,abound,arun⟩:=prepareInput_executes vista leaders
  obtain ⟨b,bbound,brun⟩:=ProtocolVista.complete_executes vista valid
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders 0 []) _ brun
  obtain ⟨c,cbound,crun⟩:=readSummary_executes vista leaders
  obtain ⟨d,dbound,drun⟩:=normal_executes vista leaders (vista.node vista.bottom).level
    [ProtocolVista.allRootLeaders vista]
  refine ⟨_,_,by dsimp only [rawBudget];omega,arun.sequence (lifted.sequence (crun.sequence drun)),?_⟩
  simp only [file]
  simpa using congrArg outputWord (CoreAudit.answer_eq_coreScheduledPlan vista leaders positive)

abbrev complete : Routine 78 := isolate completeRaw

def completeBudget (vista : Executable.Vista) (leaders : Nat) : Nat :=
  81*(rawBudget vista leaders+(inputWord vista leaders).length+3)

/-- Concrete implementation of the original coreScheduledPlan, for the
positive known leader count of the distributed model. The vista supplies its
own round; the program uses the actual core schedule and full audit. -/
theorem complete_executes (vista : Executable.Vista) (leaders : Nat) (valid : vista.valid=true)
    (positive : 0<leaders) :
    ∃ time≤ completeBudget vista leaders,
      Executes complete (inputStore 78 (inputWord vista leaders)) time
        (outputStore 78 (outputWord (Executable.coreScheduledPlan leaders vista).eval)) := by
  obtain ⟨rawTime,rawOutput,rawBound,rawRun,result⟩:=completeRaw_executes vista leaders valid positive
  obtain ⟨finish,ran,halted,stored⟩:=rawRun
  have rawHalt : ∃ time last,time≤ rawBudget vista leaders ∧
      HaltsAt completeRaw.program (inputWord vista leaders) time last ∧
      last.store 1=outputWord (Executable.coreScheduledPlan leaders vista).eval :=
    ⟨rawTime,finish,rawBound,⟨ran,halted⟩,by rw [stored];exact result⟩
  exact isolate_halts completeRaw (inputWord vista leaders)
    (outputWord (Executable.coreScheduledPlan leaders vista).eval) _ rawHalt

end Counting.StackMachine.CoreDecision
