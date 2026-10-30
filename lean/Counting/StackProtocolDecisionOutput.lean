import Counting.StackProtocolDecisionInput

namespace Counting.StackMachine.ProtocolDecision
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev emitLeader : Routine 78 := sequence (prependSaved 0)
  (sequence (move 77 0 1 79) (pushBit 1 true))

theorem emitLeader_executes (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) :
    ∃ time≤ 30*(leaders.size+1),
      Executes emitLeader (file [] [] (metadata vista leaders round flag)) time
        (file [] (outputWord (some leaders)) (metadata vista leaders round flag)) := by
  let saved:=metadata vista leaders round flag
  have a:=prependSaved_executes 0 (by decide) [] [] saved rfl rfl
  simp only [List.append_nil] at a
  have b:=move_executes 77 (0:Fin 80) 1 79 (by decide) (by decide) (by decide)
    (file (Encoding.natural.encode leaders) [] saved) (by simp [file,saved,metadata])
  have source:file (Encoding.natural.encode leaders) [] saved 0=Encoding.natural.encode leaders := by simp [file]
  have vacant:file (Encoding.natural.encode leaders) [] saved 1=[] := by simp [file]
  rw [source,vacant,List.append_nil] at b
  have middle : Function.update (Function.update (file (Encoding.natural.encode leaders) [] saved) 1
      (Encoding.natural.encode leaders)) 0 []=file [] (Encoding.natural.encode leaders) saved := by
    funext r;by_cases zero:r=0 <;> by_cases one:r=1 <;> simp [file,zero,one]
  rw [middle] at b
  have c:=pushBit_executes (1:Fin 80) true (file [] (Encoding.natural.encode leaders) saved)
  have target : Function.update (file [] (Encoding.natural.encode leaders) saved) 1
      (true::file [] (Encoding.natural.encode leaders) saved 1)=file [] (outputWord (some leaders)) saved := by
    funext r;by_cases one:r=1 <;> simp [file,one,outputWord,ProtocolAudit.outputWord,Encoding.optional]
  rw [target] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change 10*leaders.bits.length+7+1+(6*(Encoding.natural.encode leaders).length+4+1+1)≤ _
  rw [Encoding.bits_length,Encoding.natural_length]
  omega

abbrev normalInput : Routine 78 := sequence (copySaved 1)
  (sequence (prependSaved 2) (prependSaved 0))

theorem normalInput_executes (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) :
    ∃ time≤ 30*((ProtocolAudit.inputWord vista leaders round).length+1),
      Executes normalInput (file [] [] (metadata vista leaders round flag)) time
        (file (ProtocolAudit.inputWord vista leaders round) [] (metadata vista leaders round flag)) := by
  let saved:=metadata vista leaders round flag
  have a:=copySaved_executes 1 (by decide) [] [] saved rfl
  have b:=prependSaved_executes 2 (by decide) (saved 1) [] saved rfl rfl
  have c:=prependSaved_executes 0 (by decide) (Encoding.frame (saved 2)++saved 1) [] saved rfl rfl
  simp only [List.append_nil] at a
  have run:=a.sequence (b.sequence c)
  have word:Encoding.frame (saved 0)++(Encoding.frame (saved 2)++saved 1)=ProtocolAudit.inputWord vista leaders round := by
    simp [saved,metadata,ProtocolAudit.inputWord,Encoding.natural,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  change 5*(Encoding.vista.encode vista).length+2+1+(10*round.bits.length+7+1+(10*leaders.bits.length+7))≤ _
  rw [Encoding.bits_length,Encoding.bits_length]
  have length:=ProtocolAudit.inputWord_length vista leaders round
  omega

abbrev normal : Routine 78 := sequence normalInput scheduledAuditCall

def normalBudget (vista : Executable.Vista) (leaders round : Nat) : Nat :=
  30*((ProtocolAudit.inputWord vista leaders round).length+1)+ProtocolAudit.completeBudget vista leaders round+1

theorem normal_executes (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) :
    ∃ time≤ normalBudget vista leaders round,
      Executes normal (file [] [] (metadata vista leaders round flag)) time
        (file [] (outputWord (ProtocolAudit.answer vista leaders round)) (metadata vista leaders round flag)) := by
  obtain ⟨a,abound,arun⟩:=normalInput_executes vista leaders round flag
  obtain ⟨b,bbound,brun⟩:=ProtocolAudit.complete_executes vista leaders round
  have lifted:=lift_executes _ (by decide) _ _ (metadata vista leaders round flag) _ brun
  exact ⟨_,by dsimp only [normalBudget];omega,arun.sequence lifted⟩

end Counting.StackMachine.ProtocolDecision
