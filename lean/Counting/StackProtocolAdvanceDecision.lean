import Counting.StackProtocolAdvanceOutput

namespace Counting.StackMachine.ProtocolAdvance
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def decision (core : Bool) (leaders : Nat) (vista : Executable.Vista) : Option Nat :=
  if core then (Executable.coreScheduledPlan leaders vista).eval else (Executable.scheduledPlan leaders vista).eval

def decisionBudget (core : Bool) (leaders : Nat) (vista : Executable.Vista) : Nat :=
  if core then CoreDecision.completeBudget vista leaders else ProtocolDecision.completeBudget vista leaders

@[noinline] def decisionCall (core : Bool) : Routine 254 := if core then coreDecisionCall else optimizedDecisionCall

theorem decisionCall_executes (core : Bool) (leaders : Nat) (vista : Executable.Vista)
    (valid:vista.valid=true) (positive:0<leaders) (saved : Fin 8 → List Bool) :
    ∃ time≤ decisionBudget core leaders vista,
      Executes (decisionCall core) (file (ProtocolDecision.inputWord vista leaders) [] saved) time
        (file [] ((Encoding.optional Encoding.natural).encode (decision core leaders vista)) saved) := by
  cases core with
  | false=>
    simp only [decisionCall,decisionBudget,decision,Bool.false_eq_true,if_false,optimizedDecisionCall]
    obtain ⟨time,bounded,run⟩:=ProtocolDecision.complete_executes vista leaders valid
    exact ⟨time,bounded,lift_executes ProtocolDecision.complete (by decide) _ _ saved _ run⟩
  | true=>
    simp only [decisionCall,decisionBudget,decision,if_true,coreDecisionCall]
    obtain ⟨time,bounded,run⟩:=CoreDecision.complete_executes vista leaders valid positive
    exact ⟨time,bounded,lift_executes CoreDecision.complete (by decide) _ _ saved _ run⟩

abbrev prepareDecision : Routine 254 := sequence (copySaved 5) (prependSaved 1)

theorem prepareDecision_executes (leaders : Nat) (old updated : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    ∃ time≤ 20*((ProtocolDecision.inputWord updated leaders).length+1),
      Executes prepareDecision (file [] [] (metadata [] leaders old messages degree (Encoding.vista.encode updated))) time
        (file (ProtocolDecision.inputWord updated leaders) []
          (metadata [] leaders old messages degree (Encoding.vista.encode updated))) := by
  let saved:=metadata [] leaders old messages degree (Encoding.vista.encode updated)
  have a:=copySaved_executes 5 (by decide) [] [] saved rfl
  simp only [List.append_nil] at a
  have b:=prependSaved_executes 1 (by decide) (saved 5) [] saved rfl rfl
  have word:Encoding.frame (saved 1)++saved 5=ProtocolDecision.inputWord updated leaders := rfl
  rw [word] at b
  refine ⟨_,?_,a.sequence b⟩
  change 5*(Encoding.vista.encode updated).length+2+1+(10*leaders.bits.length+7)≤ _
  simp only [ProtocolDecision.inputWord,List.length_append,Encoding.natural_length,Encoding.bits_length]
  omega

abbrev finishDecision : Routine 254 := sequence (saveOutput 0) (sequence (clear 1) (emitState 5))

theorem finishDecision_executes (leaders : Nat) (old updated : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (degree : Nat) (answer : Option Nat) :
    ∃ time≤ 70*((Encoding.vista.encode updated).length+leaders.size+
        ((Encoding.optional Encoding.natural).encode answer).length+1),
      Executes finishDecision
        (file [] ((Encoding.optional Encoding.natural).encode answer)
          (metadata [] leaders old messages degree (Encoding.vista.encode updated))) time
        (file [] (outputWord (some ⟨leaders,updated,answer⟩))
          (metadata ((Encoding.optional Encoding.natural).encode answer) leaders old messages degree (Encoding.vista.encode updated))) := by
  let word:=(Encoding.optional Encoding.natural).encode answer
  let saved:=metadata [] leaders old messages degree (Encoding.vista.encode updated)
  let final:=metadata word leaders old messages degree (Encoding.vista.encode updated)
  have a:=saveOutput_executes 0 (by decide) word [] saved rfl rfl
  have savedValue:Function.update saved 0 word=final := by
    funext r;fin_cases r <;> simp [saved,final,metadata]
  rw [savedValue] at a
  have b:=clear_executes (1:Fin 256) (file [] word final)
  have source:file [] word final 1=word := by simp [file]
  rw [source] at b
  have cleaned:Function.update (file [] word final) 1 []=file [] [] final := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  rw [cleaned] at b
  obtain ⟨c,cbound,crun⟩:=emitState_executes 5 (by decide) final rfl rfl
  have output:true::(Encoding.frame (final 0)++Encoding.frame (final 1)++Encoding.frame (final 5))=
      outputWord (some ⟨leaders,updated,answer⟩) := by
    simp only [outputWord,answerCodec,Encoding.optional]
    change true::_=true::stateWord ⟨leaders,updated,answer⟩
    rw [stateWord_fields]
    rfl
  rw [output] at crun
  refine ⟨_,?_,a.sequence (b.sequence crun)⟩
  change c≤ 50*((Encoding.vista.encode updated).length+leaders.bits.length+word.length+1) at cbound
  rw [Encoding.bits_length] at cbound
  change 5*word.length+2+1+(word.length+1+1+c)≤ 70*((Encoding.vista.encode updated).length+leaders.size+word.length+1)
  omega

@[noinline] def decideAndReturn (core : Bool) : Routine 254 := sequence prepareDecision (sequence (decisionCall core) finishDecision)

def decideBudget (core : Bool) (leaders : Nat) (vista : Executable.Vista) : Nat :=
  200*((ProtocolDecision.inputWord vista leaders).length+1)+71*decisionBudget core leaders vista+2

theorem decideAndReturn_executes (core : Bool) (leaders : Nat) (old updated : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (degree : Nat) (valid:updated.valid=true) (positive:0<leaders) :
    ∃ time≤ decideBudget core leaders updated,
      Executes (decideAndReturn core)
        (file [] [] (metadata [] leaders old messages degree (Encoding.vista.encode updated))) time
        (file [] (outputWord (some ⟨leaders,updated,decision core leaders updated⟩))
          (metadata ((Encoding.optional Encoding.natural).encode (decision core leaders updated)) leaders old messages degree (Encoding.vista.encode updated))) := by
  unfold decideAndReturn
  obtain ⟨a,abound,arun⟩:=prepareDecision_executes leaders old updated messages degree
  obtain ⟨b,bbound,brun⟩:=decisionCall_executes core leaders updated valid positive
    (metadata [] leaders old messages degree (Encoding.vista.encode updated))
  have length:((Encoding.optional Encoding.natural).encode (decision core leaders updated)).length≤
      (ProtocolDecision.inputWord updated leaders).length+decisionBudget core leaders updated := by
    cases core with
    | false=>
      simp only [decision,decisionBudget,Bool.false_eq_true,if_false]
      obtain ⟨time,bounded,run⟩:=ProtocolDecision.complete_executes updated leaders valid
      exact (AuditComplete.executed_output_length ProtocolDecision.complete _ _ _ run).trans (Nat.add_le_add_left bounded _)
    | true=>
      simp only [decision,decisionBudget,if_true]
      obtain ⟨time,bounded,run⟩:=CoreDecision.complete_executes updated leaders valid positive
      exact (AuditComplete.executed_output_length CoreDecision.complete _ _ _ run).trans (Nat.add_le_add_left bounded _)
  obtain ⟨c,cbound,crun⟩:=finishDecision_executes leaders old updated messages degree (decision core leaders updated)
  have input:(ProtocolDecision.inputWord updated leaders).length=2*leaders.size+(Encoding.vista.encode updated).length+1 := by
    simp [ProtocolDecision.inputWord,Encoding.natural_length];omega
  exact ⟨_,by dsimp only [decideBudget];omega,arun.sequence (brun.sequence crun)⟩

end Counting.StackMachine.ProtocolAdvance
