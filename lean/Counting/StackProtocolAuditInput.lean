import Counting.StackProtocolAuditTransfers
import Counting.StackProtocolAuditSpec

namespace Counting.StackMachine.ProtocolAudit
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev parseInput : Routine 70 := sequence (readField 0)
  (sequence (readField 1) (moveInputSaved 2))

theorem parseInput_executes (vista : Executable.Vista) (leaders round : Nat) :
    ∃ time≤ 20*((inputWord vista leaders round).length+1),
      Executes parseInput (inputStore 70 (inputWord vista leaders round)) time
        (file [] [] (metadata vista leaders round 0 0)) := by
  let code:=Encoding.vista.encode vista
  let zero : Fin 8 → List Bool:=fun _=>[]
  let one:=Function.update zero 0 leaders.bits
  let two:=Function.update one 1 round.bits
  have a:=readField_executes 0 (by decide) leaders.bits
    (Encoding.natural.encode round++code) [] zero rfl rfl
  have b:=readField_executes 1 (by decide) round.bits code [] one
    (by simp [one,zero]) (by simp [one,zero])
  have c:=moveInputSaved_executes 2 (by decide) code [] two
    (by simp [two,one,zero]) (by simp [two,one,zero])
  have begin : file (Encoding.frame leaders.bits++(Encoding.natural.encode round++code)) [] zero=
      inputStore 70 (inputWord vista leaders round) := by
    funext r
    simp [file,inputStore,zero,inputWord,Encoding.natural,code,List.append_assoc]
  rw [begin] at a
  have middle : Encoding.natural.encode round++code=Encoding.frame round.bits++code := rfl
  rw [middle] at a
  have final : Function.update two 2 code=metadata vista leaders round 0 0 := by
    funext r;fin_cases r <;> simp [two,one,zero,metadata,code]
  rw [final] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  simp only [Encoding.bits_length]
  have size:=inputWord_length vista leaders round
  dsimp only [code]
  omega

abbrev schedulerInput : Routine 70 := sequence (prependSaved 1) (prependSaved 0)

theorem schedulerInput_executes (vista : Executable.Vista) (leaders round : Nat) :
    Executes schedulerInput (file [] [] (metadata vista leaders round 0 0))
      (10*round.size+10*leaders.size+15)
      (file (ProtocolSchedule.inputWord leaders round) [] (metadata vista leaders round 0 0)) := by
  let saved:=metadata vista leaders round 0 0
  have a:=prependSaved_executes 1 (by decide) [] [] saved rfl rfl
  have b:=prependSaved_executes 0 (by decide) (Encoding.frame (saved 1)) [] saved rfl rfl
  simp only [List.append_nil] at a
  have run:=a.sequence b
  have word : Encoding.frame (saved 0)++Encoding.frame (saved 1)=ProtocolSchedule.inputWord leaders round := rfl
  rw [word] at run
  convert run using 1
  simp [saved,metadata,Encoding.bits_length]
  omega

abbrev prepareInput : Routine 70 := sequence parseInput schedulerInput

theorem prepareInput_executes (vista : Executable.Vista) (leaders round : Nat) :
    ∃ time≤ 40*((inputWord vista leaders round).length+1),
      Executes prepareInput (inputStore 70 (inputWord vista leaders round)) time
        (file (ProtocolSchedule.inputWord leaders round) [] (metadata vista leaders round 0 0)) := by
  obtain ⟨a,abound,arun⟩:=parseInput_executes vista leaders round
  have brun:=schedulerInput_executes vista leaders round
  have size:=inputWord_length vista leaders round
  exact ⟨_,by omega,arun.sequence brun⟩

end Counting.StackMachine.ProtocolAudit
