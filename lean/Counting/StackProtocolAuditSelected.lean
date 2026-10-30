import Counting.StackProtocolAuditOutput

namespace Counting.StackMachine.ProtocolAudit
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev selected : Routine 70 := sequence prepareSelected (sequence auditCall finishAudit)

def selectedBudget (vista : Executable.Vista) (leaders candidate last : Nat) : Nat :=
  100*((AuditPrefix.inputWord vista leaders candidate last).length+1)+
    2*AuditComplete.completeBudget vista leaders candidate last+5

theorem selected_executes (vista : Executable.Vista) (leaders round candidate last : Nat) :
    ∃ time≤ selectedBudget vista leaders candidate last,
      Executes selected
        (file [] (selectedWord candidate last) (metadata vista leaders round 0 0)) time
        (file [] (outputWord (if (Executable.audit? vista leaders candidate last).isSome then some candidate else none))
          (metadata vista leaders round candidate last)) := by
  obtain ⟨a,abound,arun⟩:=prepareSelected_executes vista leaders round candidate last
  obtain ⟨b,bbound,brun⟩:=AuditComplete.complete_executes vista leaders candidate last
  have witnessLength:=AuditComplete.executed_output_length _ _ _ _ brun
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders round candidate last) _ brun
  obtain ⟨c,cbound,crun⟩:=finishAudit_executes vista leaders round candidate last
    (Executable.audit? vista leaders candidate last)
  have size:=AuditPrefix.inputWord_length vista leaders candidate last
  exact ⟨_,by dsimp only [selectedBudget];omega,arun.sequence (lifted.sequence crun)⟩

abbrev afterSchedule : Routine 70 := branchRoutine 1 selected (pushBit 1 false)

def afterScheduleBudget (vista : Executable.Vista) (leaders : Nat) (choice : Option (Nat×Nat)) : Nat :=
  match choice with
  | none=>2
  | some (candidate,last)=>selectedBudget vista leaders candidate last+1

theorem afterSchedule_executes (vista : Executable.Vista) (leaders round : Nat) (choice : Option (Nat×Nat)) :
    ∃ time output,time≤ afterScheduleBudget vista leaders choice ∧
      Executes afterSchedule
        (file [] (ProtocolSchedule.outputWord choice) (metadata vista leaders round 0 0)) time output ∧
      output 1=outputWord (choice.bind fun pair=>
        if (Executable.audit? vista leaders pair.1 pair.2).isSome then some pair.1 else none) := by
  let saved:=metadata vista leaders round 0 0
  cases choice with
  | none =>
    have a:=pushBit_executes (1:Fin 72) false (file [] [] saved)
    have target:Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [target] at a
    have popped:Function.update (file [] [false] saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_false (1:Fin 72) selected (pushBit 1 false)
      (file [] [false] saved) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,file [] [false] saved,by rfl,run,by simp [file,outputWord,Encoding.optional]⟩
  | some pair =>
    rcases pair with ⟨candidate,last⟩
    obtain ⟨time,bounded,run⟩:=selected_executes vista leaders round candidate last
    have popped:Function.update (file [] (ProtocolSchedule.outputWord (some (candidate,last))) saved) 1
        (selectedWord candidate last)=file [] (selectedWord candidate last) saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have branch:=branch_executes_true (1:Fin 72) selected (pushBit 1 false)
      (file [] (ProtocolSchedule.outputWord (some (candidate,last))) saved) _ (selectedWord candidate last) time rfl
      (by rw [popped];exact run)
    exact ⟨_,_,by dsimp only [afterScheduleBudget];omega,branch,by simp [file]⟩

end Counting.StackMachine.ProtocolAudit
