import Counting.StackAuditPostSolverSuccess
import Counting.AuditPostSolverSpec
import Counting.StackDagClean

namespace Counting.StackMachine.AuditPostSolver
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def handleBudget (anchor : Nat) (vista : Executable.Vista) : Option (Array Nat) → Nat
  | none=>2
  | some natural=>successBudget anchor vista natural+1

abbrev handleCandidate : Routine 54 := branchRoutine 1 success (pushBit 1 false)

theorem handleCandidate_executes (anchor : Nat) (vista : Executable.Vista) (natural : Option (Array Nat))
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time ≤ handleBudget anchor vista natural,
      Executes handleCandidate
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode natural) (metadata anchor vista)) time
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode
          (natural.bind (propagatedResult anchor vista))) (metadata anchor vista)) := by
  cases natural with
  | none=>
    let empty:=file [] [] (metadata anchor vista)
    have a:=pushBit_executes (1:Fin 56) false empty
    have final : Function.update empty 1 (false::empty 1)=file [] [false] (metadata anchor vista) := by
      funext r
      by_cases one:r=1 <;> simp [empty,file,one]
    rw [final] at a
    have popped : Function.update (file [] [false] (metadata anchor vista)) 1 []=empty := by
      funext r
      by_cases one:r=1 <;> simp [empty,file,one]
    have branch:=branch_executes_false (1:Fin 56) success (pushBit 1 false)
      (file [] [false] (metadata anchor vista)) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,by simp [handleBudget],branch⟩
  | some natural=>
    let word:=(Encoding.array Encoding.natural).encode natural
    obtain ⟨time,bounded,run⟩:=success_executes anchor vista natural fits valid
    have popped : Function.update (file [] (true::word) (metadata anchor vista)) 1 word=
        file [] word (metadata anchor vista) := by
      funext r
      by_cases one:r=1 <;> simp [file,one]
    have branch:=branch_executes_true (1:Fin 56) success (pushBit 1 false)
      (file [] (true::word) (metadata anchor vista)) _ word time (by simp [file]) (by rw [popped];exact run)
    exact ⟨1+time,by dsimp only [handleBudget];omega,branch⟩

abbrev finish : Routine 54 := clearRegisters [51,52]

theorem finish_executes (anchor : Nat) (vista : Executable.Vista) (word : List Bool) :
    ∃ time ≤ 2*(anchor.size+(Encoding.vista.encode vista).length+2),
      Executes finish (file [] word (metadata anchor vista)) time (outputStore 54 word) := by
  let store:=file [] word (metadata anchor vista)
  let limit:=anchor.size+(Encoding.vista.encode vista).length
  have bounded (i : Fin 56) (member : i∈([51,52] : List (Fin 56))) : (store i).length ≤ limit := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> simp [store,file,metadata,limit,Encoding.bits_length]
  obtain ⟨time,bounded,run⟩:=DagValidation.clear_selected_executes [51,52] store limit bounded
  have cleared : clearedStore [51,52] store=outputStore 54 word := by
    funext r;fin_cases r <;> simp [clearedStore,store,file,metadata,outputStore]
  rw [cleared] at run
  exact ⟨time,bounded,run⟩

abbrev complete : Routine 54 := sequence prepareInput (sequence candidateCall (sequence handleCandidate finish))

def outputWord (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat)) : List Bool :=
  (Encoding.optional (Encoding.array Encoding.natural)).encode (result vista candidate anchor values)

def completeBudget (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat)) : Nat :=
  100*((inputWord vista candidate anchor values).length+1)^2+
    500000*((AuditCandidate.inputWord values candidate).length+1)^3+
    handleBudget anchor vista (AuditCandidate.result values candidate)+
    2*(anchor.size+(Encoding.vista.encode vista).length+2)+3

/-- One actual program performs positive-integral conversion, the candidate
sum check, weight propagation and every balance check. Its sole output is
the optional propagated array; the last descendant check is separate. -/
theorem complete_executes (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat))
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time ≤ completeBudget vista candidate anchor values,
      Executes complete (inputStore 54 (inputWord vista candidate anchor values)) time
        (outputStore 54 (outputWord vista candidate anchor values)) := by
  obtain ⟨inputTime,inputBound,a⟩:=prepareInput_executes vista candidate anchor values
  obtain ⟨candidateTime,candidateBound,b⟩:=candidateCall_executes values candidate (metadata anchor vista)
  obtain ⟨bodyTime,bodyBound,c⟩:=handleCandidate_executes anchor vista (AuditCandidate.result values candidate) fits valid
  have same : (AuditCandidate.result values candidate).bind (propagatedResult anchor vista)=
      result vista candidate anchor values := rfl
  rw [same] at c
  obtain ⟨finishTime,finishBound,d⟩:=finish_executes anchor vista (outputWord vista candidate anchor values)
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  dsimp only [completeBudget]
  omega

end Counting.StackMachine.AuditPostSolver
