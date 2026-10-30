import Counting.StackProtocolDecisionTransfers

namespace Counting.StackMachine.ProtocolDecision
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def inputWord (vista : Executable.Vista) (leaders : Nat) : List Bool :=
  Encoding.natural.encode leaders++Encoding.vista.encode vista

def outputWord (result : Option Nat) : List Bool := ProtocolAudit.outputWord result

def metadata (vista : Executable.Vista) (leaders round : Nat) (flag : List Bool) : Fin 8 → List Bool :=
  ![leaders.bits,Encoding.vista.encode vista,round.bits,flag,[],[],[],[]]

abbrev prepareInput : Routine 78 := sequence (readField 0)
  (sequence (moveInputSaved 1) (copySaved 1))

theorem prepareInput_executes (vista : Executable.Vista) (leaders : Nat) :
    ∃ time≤ 20*((inputWord vista leaders).length+1),
      Executes prepareInput (inputStore 78 (inputWord vista leaders)) time
        (file (Encoding.vista.encode vista) [] (metadata vista leaders 0 [])) := by
  let code:=Encoding.vista.encode vista
  let zero : Fin 8 → List Bool:=fun _=>[]
  let one:=Function.update zero 0 leaders.bits
  let saved:=metadata vista leaders 0 []
  have a:=readField_executes 0 (by decide) leaders.bits code [] zero rfl rfl
  have b:=moveInputSaved_executes 1 (by decide) code [] one
    (by simp [one,zero]) (by simp [one,zero])
  have begin:file (Encoding.frame leaders.bits++code) [] zero=inputStore 78 (inputWord vista leaders) := by
    funext r;simp [file,inputStore,zero,inputWord,Encoding.natural,code]
  rw [begin] at a
  have final:Function.update one 1 code=saved := by
    funext r;fin_cases r <;> simp [one,zero,saved,metadata,code]
  rw [final] at b
  have c:=copySaved_executes 1 (by decide) [] [] saved rfl
  simp only [List.append_nil] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change 5*leaders.bits.length+2+1+(6*code.length+4+1+(5*code.length+2))≤ _
  simp only [inputWord,List.length_append,Encoding.natural_length,Encoding.bits_length]
  dsimp only [code]
  omega

abbrev readSummary : Routine 78 := sequence moveOutput (sequence (readField 2) (moveInputSaved 3))

theorem readSummary_executes (vista : Executable.Vista) (leaders : Nat) :
    ∃ time≤ 20*((ProtocolVista.outputWord vista).length+1),
      Executes readSummary (file [] (ProtocolVista.outputWord vista) (metadata vista leaders 0 [])) time
        (file [] [] (metadata vista leaders (vista.node vista.bottom).level [ProtocolVista.allRootLeaders vista])) := by
  let round:=(vista.node vista.bottom).level
  let flag:=ProtocolVista.allRootLeaders vista
  let zero:=metadata vista leaders 0 []
  let one:=Function.update zero 2 round.bits
  have a:=moveOutput_executes (ProtocolVista.outputWord vista) zero rfl
  have b:=readField_executes 2 (by decide) round.bits [flag] [] zero rfl rfl
  have c:=moveInputSaved_executes 3 (by decide) [flag] [] one
    (by simp [one,zero,metadata]) (by simp [one,zero,metadata])
  have final:Function.update one 3 [flag]=metadata vista leaders round [flag] := by
    funext r;fin_cases r <;> simp [one,zero,metadata]
  rw [final] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  simp only [ProtocolVista.outputWord,List.length_append,Encoding.natural_length,Encoding.bits_length,List.length_singleton]
  dsimp only [round]
  omega

end Counting.StackMachine.ProtocolDecision
