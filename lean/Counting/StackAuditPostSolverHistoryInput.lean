import Counting.StackAuditPostSolverInput

namespace Counting.StackMachine.AuditPostSolver
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev historyInput : Routine 54 := sequence (move 53 1 0 55)
  (sequence (ofProgram (ListPrograms.copyProgram 53 52 54 55))
    (sequence (frameRoutine 53 54 0 55)
      (sequence (ofProgram (ListPrograms.copyProgram 53 51 54 55)) (frameRoutine 53 54 0 55))))

/-- Reuse the retained anchor and vista to form a genuine framed input
for propagation or balance. Every copied bit and every frame is executed. -/
theorem historyInput_executes (anchor : Nat) (vista : Executable.Vista) (word : List Bool)
    (saved : Fin 6 → List Bool) (anchorAt : saved 1=anchor.bits)
    (vistaAt : saved 2=Encoding.vista.encode vista) (scratch4 : saved 4=[]) (scratch5 : saved 5=[]) :
    ∃ time ≤ 20*(word.length+(Encoding.vista.encode vista).length+anchor.size+2),
      Executes historyInput (file [] word saved) time
        (file (Encoding.natural.encode anchor++Encoding.frame (Encoding.vista.encode vista)++word) [] saved) := by
  let code:=Encoding.vista.encode vista
  let start:=file [] word saved
  have a:=move_executes 53 (1:Fin 56) 0 55 (by decide) (by decide) (by decide) start
    (by simp [start,file,scratch5])
  have source : start 1=word := by simp [start,file]
  have target : start 0=[] := by simp [start,file]
  rw [source,target,List.append_nil] at a
  let moved:=file word [] saved
  have aResult : Function.update (Function.update start 0 word) 1 []=moved := by
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> simp [start,moved,file,r0,r1]
  rw [aResult] at a
  have b:=copy_executes 53 (52:Fin 56) 54 55 (by decide) (by decide) (by decide) moved
    (by simp [moved,file,scratch5])
  have codeSource : moved 52=code := by simp [moved,file,vistaAt,code]
  have copyEmpty : moved 54=[] := by simp [moved,file,scratch4]
  rw [codeSource,copyEmpty,List.append_nil] at b
  let copied:=Function.update moved 54 code
  have c:=frame_executes_updates 53 (54:Fin 56) 0 55 (by decide) (by decide) (by decide) copied
    (by simp [copied,moved,file,scratch5])
  let framed:=file (Encoding.frame code++word) [] saved
  have cResult : Function.update (Function.update copied 54 []) 0 (Encoding.frame (copied 54)++copied 0)=framed := by
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> by_cases r54:r=54 <;>
      simp [copied,moved,framed,file,r0,r1,r54,scratch4]
  rw [cResult] at c
  change Executes _ copied (5*code.length+4) framed at c
  have d:=copy_executes 53 (51:Fin 56) 54 55 (by decide) (by decide) (by decide) framed
    (by simp [framed,file,scratch5])
  have anchorSource : framed 51=anchor.bits := by simp [framed,file,anchorAt]
  have anchorEmpty : framed 54=[] := by simp [framed,file,scratch4]
  rw [anchorSource,anchorEmpty,List.append_nil] at d
  let anchorCopied:=Function.update framed 54 anchor.bits
  have e:=frame_executes_updates 53 (54:Fin 56) 0 55 (by decide) (by decide) (by decide) anchorCopied
    (by simp [anchorCopied,framed,file,scratch5])
  have eResult : Function.update (Function.update anchorCopied 54 []) 0
      (Encoding.frame (anchorCopied 54)++anchorCopied 0)=
      file (Encoding.natural.encode anchor++Encoding.frame code++word) [] saved := by
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> by_cases r54:r=54 <;>
      simp [anchorCopied,framed,file,r0,r1,r54,scratch4,Encoding.natural,List.append_assoc]
  rw [eResult] at e
  change Executes _ anchorCopied (5*anchor.bits.length+4) _ at e
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  simp only [Encoding.bits_length]
  dsimp only [code]
  omega

end Counting.StackMachine.AuditPostSolver
