import Counting.StackProtocolDecisionOutput

namespace Counting.StackMachine.ProtocolDecision
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def roundRoles : Fin 6 ↪ Fin 80 := ⟨![72,74,1,2,3,4],by decide⟩
abbrev compareRound : Routine 78 := Compare.preservingEquality 74 roundRoles

theorem compareRound_executes (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) :
    ∃ time≤ 6*(leaders.size+round.size)+11,
      Executes compareRound (file [] [] (metadata vista leaders round flag)) time
        (file [] [decide (leaders=round)] (metadata vista leaders round flag)) := by
  let saved:=metadata vista leaders round flag
  have run:=Compare.preservingEquality_executes 74 roundRoles (file [] [] saved) rfl rfl rfl
  change Executes _ _ (Compare.preservingCost leaders.bits round.bits)
    (Function.update (file [] [] saved) 1 [decide (leaders.bits=round.bits)]) at run
  simp only [Encoding.bits_injective.eq_iff] at run
  have target:Function.update (file [] [] saved) 1 [decide (leaders=round)]=
      file [] [decide (leaders=round)] saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  rw [target] at run
  exact ⟨_,by simpa only [Encoding.bits_length] using Compare.preservingCost_le leaders.bits round.bits,run⟩

abbrev allLeaderBranch : Routine 78 := branchRoutine 75 emitLeader normal

theorem allLeaderBranch_executes (vista : Executable.Vista) (leaders round : Nat) (flag : Bool) :
    ∃ time output,time≤ normalBudget vista leaders round+30*(leaders.size+1)+1 ∧
      Executes allLeaderBranch (file [] [] (metadata vista leaders round [flag])) time output ∧
      output 1=outputWord (if flag then some leaders else ProtocolAudit.answer vista leaders round) := by
  have popped:Function.update (file [] [] (metadata vista leaders round [flag])) 75 []=
      file [] [] (metadata vista leaders round []) := by
    change Function.update (file [] [] (metadata vista leaders round [flag])) (slot 3) ([]:List Bool)=_
    rw [file_update_slot]
    congr 1
    funext r;fin_cases r <;> simp [metadata]
  cases flag with
  | false=>
    obtain ⟨time,bounded,run⟩:=normal_executes vista leaders round []
    have branch:=branch_executes_false (75:Fin 80) emitLeader normal
      (file [] [] (metadata vista leaders round [false])) _ [] time rfl
      (by rw [popped];exact run)
    exact ⟨_,_,by omega,branch,by simp [file]⟩
  | true=>
    obtain ⟨time,bounded,run⟩:=emitLeader_executes vista leaders round []
    have branch:=branch_executes_true (75:Fin 80) emitLeader normal
      (file [] [] (metadata vista leaders round [true])) _ [] time rfl
      (by rw [popped];exact run)
    exact ⟨_,_,by omega,branch,by simp [file]⟩

abbrev afterRound : Routine 78 := branchRoutine 1 allLeaderBranch normal

def decision (vista : Executable.Vista) (leaders round : Nat) (flag : Bool) : Option Nat :=
  if decide (leaders=round) && flag then some leaders else ProtocolAudit.answer vista leaders round

theorem afterRound_executes (vista : Executable.Vista) (leaders round : Nat) (flag : Bool) :
    ∃ time output,time≤ normalBudget vista leaders round+30*(leaders.size+1)+2 ∧
      Executes afterRound (file [] [decide (leaders=round)] (metadata vista leaders round [flag])) time output ∧
      output 1=outputWord (decision vista leaders round flag) := by
  have popped:Function.update (file [] [decide (leaders=round)] (metadata vista leaders round [flag])) 1 []=
      file [] [] (metadata vista leaders round [flag]) := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  by_cases same:leaders=round
  · obtain ⟨time,output,bounded,run,result⟩:=allLeaderBranch_executes vista leaders round flag
    have branch:=branch_executes_true (1:Fin 80) allLeaderBranch normal
      (file [] [decide (leaders=round)] (metadata vista leaders round [flag])) output [] time
      (by simp [file,same]) (by rw [popped];exact run)
    exact ⟨_,output,by omega,branch,by simpa only [decision,same,decide_true,Bool.true_and] using result⟩
  · obtain ⟨time,bounded,run⟩:=normal_executes vista leaders round [flag]
    have branch:=branch_executes_false (1:Fin 80) allLeaderBranch normal
      (file [] [decide (leaders=round)] (metadata vista leaders round [flag])) _ [] time
      (by simp [file,same]) (by rw [popped];exact run)
    exact ⟨_,_,by omega,branch,by simp [file,decision,same]⟩

abbrev control : Routine 78 := sequence compareRound afterRound

theorem control_executes (vista : Executable.Vista) (leaders round : Nat) (flag : Bool) :
    ∃ time output,time≤ normalBudget vista leaders round+40*(leaders.size+round.size+1)+10 ∧
      Executes control (file [] [] (metadata vista leaders round [flag])) time output ∧
      output 1=outputWord (decision vista leaders round flag) := by
  obtain ⟨a,abound,arun⟩:=compareRound_executes vista leaders round [flag]
  obtain ⟨b,output,bbound,brun,result⟩:=afterRound_executes vista leaders round flag
  exact ⟨_,output,by omega,arun.sequence brun,result⟩

/-- The control-layer decision is exactly the original scheduled solver
plan, including its all-leader early stop. -/
theorem decision_eq_scheduledPlan (vista : Executable.Vista) (leaders : Nat) :
    decision vista leaders (vista.node vista.bottom).level (ProtocolVista.allRootLeaders vista)=
      (Executable.scheduledPlan leaders vista).eval := by
  have guard:decide (leaders=(vista.node vista.bottom).level)=((vista.node vista.bottom).level==leaders) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
    exact eq_comm
  unfold decision
  rw [guard]
  dsimp only [ProtocolVista.allRootLeaders,Executable.scheduledPlan]
  split
  · rfl
  · unfold ProtocolAudit.answer
    cases Executable.candidateAt leaders (vista.node vista.bottom).level with
    | none=>rfl
    | some pair=>
      rcases pair with ⟨candidate,last⟩
      simp only [Option.bind_some,Executable.SolverPlan.eval_map]
      rfl

end Counting.StackMachine.ProtocolDecision
