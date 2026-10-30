import Counting.StackAuditCompleteTransfers

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def metadata (vista : Executable.Vista) (leaders candidate last : Nat) (anchor weights : List Bool) : Fin 8 → List Bool :=
  ![leaders.bits,candidate.bits,last.bits,Encoding.vista.encode vista,anchor,weights,[],[]]

abbrev restoreInput : Routine 62 := sequence (copySaved 3)
  (sequence (prependSaved 2) (sequence (prependSaved 1) (prependSaved 0)))

theorem restoreInput_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time≤ 30*((AuditPrefix.inputWord vista leaders candidate last).length+1),
      Executes restoreInput (file [] [] (metadata vista leaders candidate last [] [])) time
        (file (AuditPrefix.inputWord vista leaders candidate last) [] (metadata vista leaders candidate last [] [])) := by
  let saved:=metadata vista leaders candidate last [] []
  have a:=copySaved_executes 3 (by decide) [] [] saved rfl
  have b:=prependSaved_executes 2 (by decide) (saved 3) [] saved rfl rfl
  have c:=prependSaved_executes 1 (by decide) (Encoding.frame (saved 2)++saved 3) [] saved rfl rfl
  have d:=prependSaved_executes 0 (by decide)
    (Encoding.frame (saved 1)++(Encoding.frame (saved 2)++saved 3)) [] saved rfl rfl
  simp only [List.append_nil] at a
  have run:=a.sequence (b.sequence (c.sequence d))
  have word : Encoding.frame (saved 0)++(Encoding.frame (saved 1)++(Encoding.frame (saved 2)++saved 3))=
      AuditPrefix.inputWord vista leaders candidate last := by
    simp [saved,metadata,AuditPrefix.inputWord,Encoding.natural,List.append_assoc]
  rw [word] at run
  refine ⟨_,?_,run⟩
  change 5*(Encoding.vista.encode vista).length+2+1+
    (10*last.bits.length+7+1+(10*candidate.bits.length+7+1+(10*leaders.bits.length+7)))≤ _
  simp only [Encoding.bits_length]
  have size:=AuditPrefix.inputWord_length vista leaders candidate last
  omega

abbrev parseInput : Routine 62 := sequence (readField 0)
  (sequence (readField 1) (sequence (readField 2) (moveInputSaved 3)))

theorem parseInput_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time≤ 20*((AuditPrefix.inputWord vista leaders candidate last).length+1),
      Executes parseInput (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) time
        (file [] [] (metadata vista leaders candidate last [] [])) := by
  let code:=Encoding.vista.encode vista
  let zero : Fin 8 → List Bool:=fun _=>[]
  let one:=Function.update zero 0 leaders.bits
  let two:=Function.update one 1 candidate.bits
  let three:=Function.update two 2 last.bits
  have a:=readField_executes 0 (by decide) leaders.bits
    (Encoding.natural.encode candidate++Encoding.natural.encode last++code) [] zero rfl rfl
  have b:=readField_executes 1 (by decide) candidate.bits
    (Encoding.natural.encode last++code) [] one (by simp [one,zero]) (by simp [one,zero])
  have c:=readField_executes 2 (by decide) last.bits code [] two
    (by simp [two,one,zero]) (by simp [two,one,zero])
  have d:=moveInputSaved_executes 3 (by decide) code [] three
    (by simp [three,two,one,zero]) (by simp [three,two,one,zero])
  have begin : file (Encoding.frame leaders.bits++
      (Encoding.natural.encode candidate++Encoding.natural.encode last++code)) [] zero=
      inputStore 62 (AuditPrefix.inputWord vista leaders candidate last) := by
    funext r
    simp [file,inputStore,zero,AuditPrefix.inputWord,Encoding.natural,code,List.append_assoc]
  rw [begin] at a
  have middle1 : Encoding.natural.encode candidate++Encoding.natural.encode last++code=
      Encoding.frame candidate.bits++(Encoding.natural.encode last++code) := by
    simp [Encoding.natural,List.append_assoc]
  rw [middle1] at a
  have middle2 : Encoding.natural.encode last++code=Encoding.frame last.bits++code := rfl
  rw [middle2] at b
  have final : Function.update three 3 code=metadata vista leaders candidate last [] [] := by
    funext r;fin_cases r <;> simp [three,two,one,zero,metadata,code]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp only [Encoding.bits_length]
  have size:=AuditPrefix.inputWord_length vista leaders candidate last
  dsimp only [code]
  omega

abbrev prepareInput : Routine 62 := sequence parseInput restoreInput

/-- Retain only the actual local input parameters while restoring the
complete original input for the prefix checker. Every transfer is executed. -/
theorem prepareInput_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time≤ 51*((AuditPrefix.inputWord vista leaders candidate last).length+1),
      Executes prepareInput (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) time
        (file (AuditPrefix.inputWord vista leaders candidate last) [] (metadata vista leaders candidate last [] [])) := by
  obtain ⟨a,abound,arun⟩:=parseInput_executes vista leaders candidate last
  obtain ⟨b,bbound,brun⟩:=restoreInput_executes vista leaders candidate last
  exact ⟨_,by omega,arun.sequence brun⟩

end Counting.StackMachine.AuditComplete
