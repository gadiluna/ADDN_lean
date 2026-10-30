import Counting.StackProtocolAuditInput

namespace Counting.StackMachine.ProtocolAudit
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev parseSelected : Routine 70 := sequence moveOutput (sequence (readField 3) (readField 4))

theorem parseSelected_executes (vista : Executable.Vista) (leaders round candidate last : Nat) :
    ∃ time≤ 20*((selectedWord candidate last).length+1),
      Executes parseSelected
        (file [] (selectedWord candidate last) (metadata vista leaders round 0 0)) time
        (file [] [] (metadata vista leaders round candidate last)) := by
  let zero:=metadata vista leaders round 0 0
  let one:=Function.update zero 3 candidate.bits
  have a:=moveOutput_executes (selectedWord candidate last) zero rfl
  have b:=readField_executes 3 (by decide) candidate.bits (Encoding.natural.encode last) [] zero rfl rfl
  have c:=readField_executes 4 (by decide) last.bits [] [] one
    (by simp [one,zero,metadata]) (by simp [one,zero,metadata])
  have input : selectedWord candidate last=Encoding.frame candidate.bits++Encoding.natural.encode last := rfl
  rw [input] at a
  simp only [List.append_nil] at c
  have final : Function.update one 4 last.bits=metadata vista leaders round candidate last := by
    funext r;fin_cases r <;> simp [one,zero,metadata]
  rw [final] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  rw [←input]
  simp only [Encoding.bits_length]
  have size:=selectedWord_length candidate last
  omega

abbrev auditInput : Routine 70 := sequence (copySaved 2)
  (sequence (prependSaved 4) (sequence (prependSaved 3) (prependSaved 0)))

theorem auditInput_executes (vista : Executable.Vista) (leaders round candidate last : Nat) :
    ∃ time≤ 30*((AuditPrefix.inputWord vista leaders candidate last).length+1),
      Executes auditInput (file [] [] (metadata vista leaders round candidate last)) time
        (file (AuditPrefix.inputWord vista leaders candidate last) [] (metadata vista leaders round candidate last)) := by
  let saved:=metadata vista leaders round candidate last
  have a:=copySaved_executes 2 (by decide) [] [] saved rfl
  have b:=prependSaved_executes 4 (by decide) (saved 2) [] saved rfl rfl
  have c:=prependSaved_executes 3 (by decide) (Encoding.frame (saved 4)++saved 2) [] saved rfl rfl
  have d:=prependSaved_executes 0 (by decide)
    (Encoding.frame (saved 3)++(Encoding.frame (saved 4)++saved 2)) [] saved rfl rfl
  simp only [List.append_nil] at a
  have run:=a.sequence (b.sequence (c.sequence d))
  have word : Encoding.frame (saved 0)++(Encoding.frame (saved 3)++(Encoding.frame (saved 4)++saved 2))=
      AuditPrefix.inputWord vista leaders candidate last := by
    simp [saved,metadata,AuditPrefix.inputWord,Encoding.natural,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  change 5*(Encoding.vista.encode vista).length+2+1+
    (10*last.bits.length+7+1+(10*candidate.bits.length+7+1+(10*leaders.bits.length+7)))≤ _
  simp only [Encoding.bits_length]
  have size:=AuditPrefix.inputWord_length vista leaders candidate last
  omega

abbrev prepareSelected : Routine 70 := sequence parseSelected auditInput

theorem prepareSelected_executes (vista : Executable.Vista) (leaders round candidate last : Nat) :
    ∃ time≤ 51*((AuditPrefix.inputWord vista leaders candidate last).length+1),
      Executes prepareSelected
        (file [] (selectedWord candidate last) (metadata vista leaders round 0 0)) time
        (file (AuditPrefix.inputWord vista leaders candidate last) [] (metadata vista leaders round candidate last)) := by
  obtain ⟨a,abound,arun⟩:=parseSelected_executes vista leaders round candidate last
  obtain ⟨b,bbound,brun⟩:=auditInput_executes vista leaders round candidate last
  have selected: (selectedWord candidate last).length≤ (AuditPrefix.inputWord vista leaders candidate last).length := by
    rw [selectedWord_length,AuditPrefix.inputWord_length]
    omega
  exact ⟨_,by omega,arun.sequence brun⟩

end Counting.StackMachine.ProtocolAudit
