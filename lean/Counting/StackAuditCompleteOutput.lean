import Counting.StackAuditCompleteBridges
import Counting.StackAuditCompleteSpec

namespace Counting.StackMachine.AuditComplete
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev emitWitness : Routine 62 := sequence (copySaved 5)
  (sequence (prependSaved 4) (sequence (move 61 0 1 63) (pushBit 1 true)))

theorem emitWitness_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (weights : Array Nat) :
    ∃ time≤ 40*(anchor.size+((Encoding.array Encoding.natural).encode weights).length+1),
      Executes emitWitness
        (file [] [] (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) time
        (file [] (witnessWord (some ⟨anchor,weights⟩))
          (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) := by
  let word:=(Encoding.array Encoding.natural).encode weights
  let saved:=metadata vista leaders candidate last anchor.bits word
  have a:=copySaved_executes 5 (by decide) [] [] saved rfl
  simp only [List.append_nil] at a
  have b:=prependSaved_executes 4 (by decide) (saved 5) [] saved rfl rfl
  let payload:=Encoding.natural.encode anchor++word
  have encoded : Encoding.frame (saved 4)++saved 5=payload := by simp [saved,metadata,payload,Encoding.natural]
  rw [encoded] at b
  have c:=move_executes 61 (0:Fin 64) 1 63 (by decide) (by decide) (by decide)
    (file payload [] saved) (by simp [file,saved,metadata])
  have source:file payload [] saved 0=payload := by simp [file]
  have vacant:file payload [] saved 1=[] := by simp [file]
  rw [source,vacant,List.append_nil] at c
  have moved : Function.update (Function.update (file payload [] saved) 1 payload) 0 []=
      file [] payload saved := by
    funext r;by_cases zero:r=0 <;> by_cases one:r=1 <;> simp [file,zero,one]
  rw [moved] at c
  have d:=pushBit_executes (1:Fin 64) true (file [] payload saved)
  have pushed : Function.update (file [] payload saved) 1 (true::file [] payload saved 1)=
      file [] (witnessWord (some ⟨anchor,weights⟩)) saved := by
    funext r;by_cases one:r=1 <;> simp [file,one,witnessWord,payload,word]
  rw [pushed] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp [saved,metadata,payload,word,Encoding.natural_length,List.length_append,Encoding.bits_length]
  omega

abbrev finishDescendant : Routine 62 := branchRoutine 1 emitWitness (pushBit 1 false)

theorem finishDescendant_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (weights : Array Nat) (accepted : Bool) :
    ∃ time≤ 41*(anchor.size+((Encoding.array Encoding.natural).encode weights).length+1),
      Executes finishDescendant
        (file [] [accepted] (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) time
        (file [] (witnessWord (if accepted then some ⟨anchor,weights⟩ else none))
          (metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights))) := by
  let saved:=metadata vista leaders candidate last anchor.bits ((Encoding.array Encoding.natural).encode weights)
  have popped : Function.update (file [] [accepted] saved) 1 []=file [] [] saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  cases accepted with
  | false =>
    have a:=pushBit_executes (1:Fin 64) false (file [] [] saved)
    have result : Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [result] at a
    have run:=branch_executes_false (1:Fin 64) emitWitness (pushBit 1 false)
      (file [] [false] saved) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,by omega,run⟩
  | true =>
    obtain ⟨time,bounded,a⟩:=emitWitness_executes vista leaders candidate last anchor weights
    have run:=branch_executes_true (1:Fin 64) emitWitness (pushBit 1 false)
      (file [] [true] saved) _ [] time (by simp [file]) (by rw [popped];exact a)
    exact ⟨_,by omega,run⟩

end Counting.StackMachine.AuditComplete
