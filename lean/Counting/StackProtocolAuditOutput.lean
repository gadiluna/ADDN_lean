import Counting.StackProtocolAuditSelectedInput

namespace Counting.StackMachine.ProtocolAudit
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev emitCandidate : Routine 70 := sequence (prependSaved 3)
  (sequence (move 69 0 1 71) (pushBit 1 true))

theorem emitCandidate_executes (vista : Executable.Vista) (leaders round candidate last : Nat) :
    ∃ time≤ 30*(candidate.size+1),
      Executes emitCandidate (file [] [] (metadata vista leaders round candidate last)) time
        (file [] (outputWord (some candidate)) (metadata vista leaders round candidate last)) := by
  let saved:=metadata vista leaders round candidate last
  have a:=prependSaved_executes 3 (by decide) [] [] saved rfl rfl
  simp only [List.append_nil] at a
  have b:=move_executes 69 (0:Fin 72) 1 71 (by decide) (by decide) (by decide)
    (file (Encoding.natural.encode candidate) [] saved) (by simp [file,saved,metadata])
  have source:file (Encoding.natural.encode candidate) [] saved 0=Encoding.natural.encode candidate := by simp [file]
  have vacant:file (Encoding.natural.encode candidate) [] saved 1=[] := by simp [file]
  rw [source,vacant,List.append_nil] at b
  have middle : Function.update (Function.update (file (Encoding.natural.encode candidate) [] saved) 1
      (Encoding.natural.encode candidate)) 0 []=file [] (Encoding.natural.encode candidate) saved := by
    funext r;by_cases zero:r=0 <;> by_cases one:r=1 <;> simp [file,zero,one]
  rw [middle] at b
  have c:=pushBit_executes (1:Fin 72) true (file [] (Encoding.natural.encode candidate) saved)
  have target : Function.update (file [] (Encoding.natural.encode candidate) saved) 1
      (true::file [] (Encoding.natural.encode candidate) saved 1)=file [] (outputWord (some candidate)) saved := by
    funext r;by_cases one:r=1 <;> simp [file,one,outputWord,Encoding.optional]
  rw [target] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change 10*candidate.bits.length+7+1+(6*(Encoding.natural.encode candidate).length+4+1+1)≤ _
  rw [Encoding.bits_length,Encoding.natural_length]
  omega

abbrev acceptAudit : Routine 70 := sequence (clear 1) emitCandidate
abbrev finishAudit : Routine 70 := branchRoutine 1 acceptAudit (pushBit 1 false)

theorem finishAudit_executes (vista : Executable.Vista) (leaders round candidate last : Nat)
    (result : Option Executable.AuditWitness) :
    ∃ time≤ (AuditComplete.witnessWord result).length+31*(candidate.size+1)+3,
      Executes finishAudit
        (file [] (AuditComplete.witnessWord result) (metadata vista leaders round candidate last)) time
        (file [] (outputWord (if result.isSome then some candidate else none))
          (metadata vista leaders round candidate last)) := by
  let saved:=metadata vista leaders round candidate last
  cases result with
  | none =>
    have a:=pushBit_executes (1:Fin 72) false (file [] [] saved)
    have target:Function.update (file [] [] saved) 1 (false::file [] [] saved 1)=file [] [false] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [target] at a
    have popped:Function.update (file [] [false] saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_false (1:Fin 72) acceptAudit (pushBit 1 false)
      (file [] [false] saved) _ [] 1 (by simp [file]) (by rw [popped];exact a)
    exact ⟨2,by simp [AuditComplete.witnessWord],run⟩
  | some witness =>
    let payload:=Encoding.natural.encode witness.anchor++(Encoding.array Encoding.natural).encode witness.weights
    have a:=clear_executes (1:Fin 72) (file [] payload saved)
    have source:file [] payload saved 1=payload := by simp [file]
    rw [source] at a
    have emptied:Function.update (file [] payload saved) 1 []=file [] [] saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    rw [emptied] at a
    obtain ⟨b,bbound,brun⟩:=emitCandidate_executes vista leaders round candidate last
    have cleared:=a.sequence brun
    have popped:Function.update (file [] (true::payload) saved) 1 payload=file [] payload saved := by
      funext r;by_cases one:r=1 <;> simp [file,one]
    have run:=branch_executes_true (1:Fin 72) acceptAudit (pushBit 1 false)
      (file [] (true::payload) saved) _ payload _ (by simp [file]) (by rw [popped];exact cleared)
    refine ⟨_,?_,run⟩
    change 1+(payload.length+1+1+b)≤ (true::payload).length+31*(candidate.size+1)+3
    simp only [List.length_cons]
    omega

end Counting.StackMachine.ProtocolAudit
