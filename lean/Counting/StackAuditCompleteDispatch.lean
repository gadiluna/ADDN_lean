import Counting.StackAuditCompleteAnchor
import Counting.StackAuditCompleteSuffix

namespace Counting.StackMachine.AuditComplete
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev successfulPrefix : Routine 62 := sequence decrementAnchor selected

def dispatchBudget (vista : Executable.Vista) (leaders candidate last : Nat) : Option Nat → Nat
  | none=>2
  | some anchor=>100*((anchor+1).size+anchor.size+1)+selectedBudget vista leaders candidate last anchor+2

def answerAfterPrefix (vista : Executable.Vista) (leaders candidate last : Nat) : Option Nat → Option Executable.AuditWitness
  | none=>none
  | some anchor=>Executable.auditSuffix? vista candidate last anchor (solvedValues vista leaders anchor)

def metadataAfterPrefix (vista : Executable.Vista) (leaders candidate last : Nat) : Option Nat → Fin 8 → List Bool
  | none=>metadata vista leaders candidate last [] []
  | some anchor=>metadata vista leaders candidate last anchor.bits
      (optionalWeightsWord (AuditPostSolver.result vista candidate anchor (solvedValues vista leaders anchor)))

abbrev dispatchPrefix : Routine 62 := branchRoutine 1 (pushBit 1 false) successfulPrefix

theorem dispatchPrefix_executes (vista : Executable.Vista) (leaders candidate last : Nat) (choice : Option Nat)
    (found : Executable.auditPrefix? vista leaders candidate last=choice) :
    ∃ time≤ dispatchBudget vista leaders candidate last choice,
      Executes dispatchPrefix
        (file [] [decide (choice=none)] (metadata vista leaders candidate last (AuditPrefix.anchorCode choice).bits [])) time
        (file [] (witnessWord (answerAfterPrefix vista leaders candidate last choice))
          (metadataAfterPrefix vista leaders candidate last choice)) := by
  cases choice with
  | none =>
    let saved:=metadata vista leaders candidate last [] []
    have a:=pushBit_executes (1:Fin 64) false (file [] [] saved)
    have result : Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [result] at a
    have popped : Function.update (file [] [true] saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_true (1:Fin 64) (pushBit 1 false) successfulPrefix
      (file [] [true] saved) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,by simp [dispatchBudget],run⟩
  | some anchor =>
    obtain ⟨valid,anchorLast,lastNodes⟩:=prefix_success_bounds vista leaders candidate last anchor found
    obtain ⟨a,abound,arun⟩:=decrementAnchor_executes vista leaders candidate last anchor
    obtain ⟨b,bbound,brun⟩:=selected_executes vista leaders candidate last anchor (by omega) (by omega) valid
    let saved:=metadata vista leaders candidate last (anchor+1).bits []
    have popped : Function.update (file [] [false] saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_false (1:Fin 64) (pushBit 1 false) successfulPrefix
      (file [] [false] saved) _ [] _ (by simp [file]) (by rw [popped];exact arun.sequence brun)
    exact ⟨_,by dsimp only [dispatchBudget];omega,run⟩

abbrev afterPrefix : Routine 62 := sequence readAnchor
  (sequence (DagValidation.emptyFlag 60 1) dispatchPrefix)

def afterPrefixBudget (vista : Executable.Vista) (leaders candidate last : Nat) (choice : Option Nat) : Nat :=
  20*((AuditPrefix.anchorCode choice).size+1)+dispatchBudget vista leaders candidate last choice+5

/-- Decode the concrete choice answer and dispatch to the unique solver
branch only after the actual choice has accepted. -/
theorem afterPrefix_executes (vista : Executable.Vista) (leaders candidate last : Nat) (choice : Option Nat)
    (found : Executable.auditPrefix? vista leaders candidate last=choice) :
    ∃ time≤ afterPrefixBudget vista leaders candidate last choice,
      Executes afterPrefix
        (file [] (Encoding.optionalNatural.encode choice) (metadata vista leaders candidate last [] [])) time
        (file [] (witnessWord (answerAfterPrefix vista leaders candidate last choice))
          (metadataAfterPrefix vista leaders candidate last choice)) := by
  obtain ⟨a,abound,arun⟩:=readAnchor_executes vista leaders candidate last choice
  let saved:=metadata vista leaders candidate last (AuditPrefix.anchorCode choice).bits []
  have b:=DagValidation.emptyFlag_executes (60:Fin 64) 1 (file [] [] saved)
  have source : file [] [] saved 60=(AuditPrefix.anchorCode choice).bits := by simp [file,saved,metadata]
  have vacant : file [] [] saved 1=[] := by simp [file]
  rw [source,vacant] at b
  have zero : (AuditPrefix.anchorCode choice).bits=[] ↔ choice=none := by
    cases choice with
    | none=>simp [AuditPrefix.anchorCode]
    | some anchor=>
      have nonempty:(anchor+1).bits≠[] := by
        intro empty
        have equal:=congrArg Encoding.value empty
        simp only [Encoding.value_bits,Encoding.value] at equal
        omega
      simp [AuditPrefix.anchorCode,nonempty]
  simp only [zero] at b
  have marked : Function.update (file [] [] saved) 1 [decide (choice=none)]=
      file [] [decide (choice=none)] saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  rw [marked] at b
  obtain ⟨c,cbound,crun⟩:=dispatchPrefix_executes vista leaders candidate last choice found
  have flagCost : DagValidation.emptyFlagCost (AuditPrefix.anchorCode choice).bits≤ 3 := by
    unfold DagValidation.emptyFlagCost;split <;> omega
  exact ⟨_,by dsimp only [afterPrefixBudget];omega,arun.sequence (b.sequence crun)⟩

end Counting.StackMachine.AuditComplete
