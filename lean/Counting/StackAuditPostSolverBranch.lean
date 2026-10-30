import Counting.StackAuditPostSolverInput

namespace Counting.StackMachine.AuditPostSolver
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev saveWeights : Routine 54 := ofProgram (ListPrograms.copyProgram 53 1 53 55)

theorem saveWeights_executes (anchor : Nat) (vista : Executable.Vista) (word : List Bool) :
    Executes saveWeights (file [] word (metadata anchor vista)) (5*word.length+2)
      (file [] word (Function.update (metadata anchor vista) 3 word)) := by
  have run:=copy_executes 53 (1:Fin 56) 53 55 (by decide) (by decide) (by decide)
    (file [] word (metadata anchor vista)) (by simp [file,metadata])
  have source : file [] word (metadata anchor vista) 1=word := by simp [file]
  have target : file [] word (metadata anchor vista) 53=[] := by simp [file,metadata]
  rw [source,target,List.append_nil] at run
  have result : Function.update (file [] word (metadata anchor vista)) 53 word=
      file [] word (Function.update (metadata anchor vista) 3 word) := by
    funext r;fin_cases r <;> simp [file,metadata]
  rw [result] at run
  exact run

abbrev keepWeights : Routine 54 := sequence (move 53 53 1 55) (pushBit 1 true)
abbrev rejectWeights : Routine 54 := sequence (clear 53) (pushBit 1 false)
abbrev chooseBalance : Routine 54 := branchRoutine 1 keepWeights rejectWeights

/-- A physical Boolean branch returns the saved weights or erases them;
the optional-result tag is written by the machine in both branches. -/
theorem chooseBalance_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) (accepted : Bool) :
    ∃ time ≤ 10*(((Encoding.array Encoding.natural).encode weights).length+1),
      Executes chooseBalance
        (file [] [accepted] (Function.update (metadata anchor vista) 3 ((Encoding.array Encoding.natural).encode weights))) time
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode (if accepted then some weights else none))
          (metadata anchor vista)) := by
  let word:=(Encoding.array Encoding.natural).encode weights
  let saved:=Function.update (metadata anchor vista) 3 word
  let popped:=file [] [] saved
  have cleared (bit : Bool) : Function.update (file [] [bit] saved) 1 []=popped := by
    funext r
    by_cases one:r=1 <;> simp [popped,file,one]
  cases accepted with
  | true=>
    have a:=move_executes 53 (53:Fin 56) 1 55 (by decide) (by decide) (by decide) popped
      (by simp [popped,file,saved,metadata])
    have source : popped 53=word := by simp [popped,file,saved]
    have target : popped 1=[] := by simp [popped,file]
    rw [source,target,List.append_nil] at a
    let moved:=file [] word (metadata anchor vista)
    have result : Function.update (Function.update popped 1 word) 53 []=moved := by
      funext r;fin_cases r <;> simp [popped,moved,file,saved,metadata]
    rw [result] at a
    have b:=pushBit_executes (1:Fin 56) true moved
    have final : Function.update moved 1 (true::moved 1)=file [] (true::word) (metadata anchor vista) := by
      funext r
      by_cases one:r=1 <;> simp [moved,file,one]
    rw [final] at b
    have branch:=branch_executes_true (1:Fin 56) keepWeights rejectWeights
      (file [] [true] saved) _ [] _ (by simp [file]) (by rw [cleared];exact a.sequence b)
    exact ⟨_,by dsimp only [word];omega,branch⟩
  | false=>
    have a:=clear_executes (53:Fin 56) popped
    have source : popped 53=word := by simp [popped,file,saved]
    rw [source] at a
    let erased:=file [] [] (metadata anchor vista)
    have result : Function.update popped 53 []=erased := by
      funext r;fin_cases r <;> simp [popped,erased,file,saved,metadata]
    rw [result] at a
    have b:=pushBit_executes (1:Fin 56) false erased
    have final : Function.update erased 1 (false::erased 1)=file [] [false] (metadata anchor vista) := by
      funext r
      by_cases one:r=1 <;> simp [erased,file,one]
    rw [final] at b
    have branch:=branch_executes_false (1:Fin 56) keepWeights rejectWeights
      (file [] [false] saved) _ [] _ (by simp [file]) (by rw [cleared];exact a.sequence b)
    exact ⟨_,by dsimp only [word];omega,branch⟩

end Counting.StackMachine.AuditPostSolver
