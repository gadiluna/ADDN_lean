import Counting.StackAuditCompleteInput

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev solverInput : Routine 62 := sequence (copySaved 3)
  (sequence (prependSaved 0) (prependSaved 4))

/-- Build the actual anchor-system input from the retained local data. -/
theorem solverInput_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat) :
    ∃ time≤ 30*((AnchorMatrix.inputWord anchor leaders vista).length+1),
      Executes solverInput (file [] [] (metadata vista leaders candidate last anchor.bits [])) time
        (file (AnchorMatrix.inputWord anchor leaders vista) [] (metadata vista leaders candidate last anchor.bits [])) := by
  let saved:=metadata vista leaders candidate last anchor.bits []
  have a:=copySaved_executes 3 (by decide) [] [] saved rfl
  simp only [List.append_nil] at a
  have b:=prependSaved_executes 0 (by decide) (saved 3) [] saved rfl rfl
  have c:=prependSaved_executes 4 (by decide) (Encoding.frame (saved 0)++saved 3) [] saved rfl rfl
  have run:=a.sequence (b.sequence c)
  have word : Encoding.frame (saved 4)++(Encoding.frame (saved 0)++saved 3)=
      AnchorMatrix.inputWord anchor leaders vista := by
    simp [saved,metadata,AnchorMatrix.inputWord,Encoding.natural,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  simp [saved,metadata,AnchorMatrix.inputWord,Encoding.natural_length,List.length_append,Encoding.bits_length]
  omega

abbrev postSolverInput : Routine 62 := sequence moveOutput
  (sequence (prependSaved 3) (sequence (prependSaved 4) (prependSaved 1)))

/-- Physically frame the genuine solver output for the complete post-solver. -/
theorem postSolverInput_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (values : Option (Array Rat)) :
    ∃ time≤ 30*((AuditPostSolver.inputWord vista candidate anchor values).length+1),
      Executes postSolverInput
        (file [] (AuditPositive.inputWord values) (metadata vista leaders candidate last anchor.bits [])) time
        (file (AuditPostSolver.inputWord vista candidate anchor values) []
          (metadata vista leaders candidate last anchor.bits [])) := by
  let saved:=metadata vista leaders candidate last anchor.bits []
  let payload:=AuditPositive.inputWord values
  have a:=moveOutput_executes payload saved rfl
  have b:=prependSaved_executes 3 (by decide) payload [] saved rfl rfl
  have c:=prependSaved_executes 4 (by decide) (Encoding.frame (saved 3)++payload) [] saved rfl rfl
  have d:=prependSaved_executes 1 (by decide)
    (Encoding.frame (saved 4)++(Encoding.frame (saved 3)++payload)) [] saved rfl rfl
  have run:=a.sequence (b.sequence (c.sequence d))
  have word : Encoding.frame (saved 1)++(Encoding.frame (saved 4)++(Encoding.frame (saved 3)++payload))=
      AuditPostSolver.inputWord vista candidate anchor values := by
    simp [saved,metadata,AuditPostSolver.inputWord,Encoding.natural,payload,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  simp [saved,metadata,AuditPostSolver.inputWord,Encoding.natural_length,Encoding.frame_length,
    List.length_append,Encoding.bits_length,payload]
  omega

abbrev descendantInput : Routine 62 := sequence (saveOutput 5)
  (sequence moveOutput (sequence (prependSaved 3) (sequence (prependSaved 2) (prependSaved 4))))

/-- Retain the propagated weights for the output witness and construct the
complete descendant input. The weight word is copied by machine steps. -/
theorem descendantInput_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (weights : Array Nat) :
    ∃ time≤ 40*((AuditDescendant.completeInputWord vista weights anchor last).length+1),
      Executes descendantInput
        (file [] ((Encoding.array Encoding.natural).encode weights)
          (metadata vista leaders candidate last anchor.bits [])) time
        (file (AuditDescendant.completeInputWord vista weights anchor last) []
          (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) := by
  let payload:=(Encoding.array Encoding.natural).encode weights
  let before:=metadata vista leaders candidate last anchor.bits []
  let saved:=metadata vista leaders candidate last anchor.bits payload
  have a:=saveOutput_executes 5 (by decide) payload [] before rfl rfl
  have stored : Function.update before 5 payload=saved := by
    funext r;fin_cases r <;> simp [before,saved,metadata]
  rw [stored] at a
  have b:=moveOutput_executes payload saved rfl
  have c:=prependSaved_executes 3 (by decide) payload [] saved rfl rfl
  have d:=prependSaved_executes 2 (by decide) (Encoding.frame (saved 3)++payload) [] saved rfl rfl
  have e:=prependSaved_executes 4 (by decide)
    (Encoding.frame (saved 2)++(Encoding.frame (saved 3)++payload)) [] saved rfl rfl
  have run:=a.sequence (b.sequence (c.sequence (d.sequence e)))
  have word : Encoding.frame (saved 4)++(Encoding.frame (saved 2)++(Encoding.frame (saved 3)++payload))=
      AuditDescendant.completeInputWord vista weights anchor last := by
    simp [saved,metadata,AuditDescendant.completeInputWord,Encoding.natural,payload,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  simp [saved,metadata,AuditDescendant.completeInputWord,Encoding.natural_length,Encoding.frame_length,
    List.length_append,Encoding.bits_length,payload]
  omega

end Counting.StackMachine.AuditComplete
