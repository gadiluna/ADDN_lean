import Counting.StackProtocolAdvanceDecision
import Counting.StackProtocolUpdateComplete

namespace Counting.StackMachine.ProtocolAdvance
open Routine Executable EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

abbrev prepareUpdate : Routine 254 := sequence (prependSaved 4)
  (sequence (prependSaved 3) (prependSaved 2))

theorem prepareUpdate_executes (leaders : Nat) (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    ∃time≤ 20*((ProtocolUpdate.inputWord old messages degree).length+1),
      Executes prepareUpdate (file [] [] (metadata [] leaders old messages degree [])) time
        (file (ProtocolUpdate.inputWord old messages degree) [] (metadata [] leaders old messages degree [])) := by
  let saved:=metadata [] leaders old messages degree []
  have a:=prependSaved_executes 4 (by decide) [] [] saved rfl rfl
  simp only [List.append_nil] at a
  have b:=prependSaved_executes 3 (by decide) (Encoding.frame (saved 4)) [] saved rfl rfl
  have c:=prependSaved_executes 2 (by decide) (Encoding.frame (saved 3)++Encoding.frame (saved 4)) [] saved rfl rfl
  have word:Encoding.frame (saved 2)++(Encoding.frame (saved 3)++Encoding.frame (saved 4))=
      ProtocolUpdate.inputWord old messages degree := rfl
  rw [word] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  simp only [ProtocolUpdate.inputWord_eq,List.length_append,Encoding.frame_length,Encoding.natural_length]
  change 10*degree.bits.length+7+1+(10*(messagesCodec.encode messages).length+7+1+
    (10*(Encoding.vista.encode old).length+7))≤ _
  rw [Encoding.bits_length]
  change _≤ 20*(2*(Encoding.vista.encode old).length+1+(2*(messagesCodec.encode messages).length+1)+(2*degree.size+1)+1)
  omega

@[noinline] def updateCall : Routine 254 := relocate ProtocolUpdate.complete (roles 158 (by decide))
abbrev saveUpdated : Routine 254 := sequence moveOutput (moveInputSaved 5)

theorem saveUpdated_executes (leaders : Nat) (old updated : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    Executes saveUpdated (file [] (Encoding.vista.encode updated) (metadata [] leaders old messages degree []))
      (12*(Encoding.vista.encode updated).length+9)
      (file [] [] (metadata [] leaders old messages degree (Encoding.vista.encode updated))) := by
  let saved:=metadata [] leaders old messages degree []
  have a:=moveOutput_executes (Encoding.vista.encode updated) saved rfl
  have b:=moveInputSaved_executes 5 (by decide) (Encoding.vista.encode updated) [] saved rfl rfl
  have final:Function.update saved 5 (Encoding.vista.encode updated)=
      metadata [] leaders old messages degree (Encoding.vista.encode updated) := by
    funext r;fin_cases r <;> simp [saved,metadata]
  rw [final] at b
  convert a.sequence b using 1
  omega

@[noinline] def useUpdated (core : Bool) : Routine 254 := sequence saveUpdated (decideAndReturn core)
abbrev reject : Routine 254 := pushBit 1 false
@[noinline] def afterUpdate (core : Bool) : Routine 254 := branchRoutine 1 (useUpdated core) reject
@[noinline] def updateAndDecide (core : Bool) : Routine 254 := sequence prepareUpdate (sequence updateCall (afterUpdate core))

def updateBudget (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Nat :=
  ProtocolUpdate.completeCoefficient*((ProtocolUpdate.inputWord old messages degree).length+1)^272

def activeBudget (core : Bool) (leaders : Nat) (old updated : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Nat :=
  20*((ProtocolUpdate.inputWord old messages degree).length+1)+updateBudget old messages degree+
    12*(Encoding.vista.encode updated).length+decideBudget core leaders updated+20

theorem updateAndDecide_executes (core : Bool) (leaders : Nat) (old updated : Vista)
    (messages : List (Vista×Nat)) (degree : Nat) (valid:old.valid=true) (positive:0<leaders)
    (received:∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧ (m.1.node m.1.bottom).level=(old.node old.bottom).level)
    (success:updateVista? old messages degree=some updated) :
    ∃time≤ activeBudget core leaders old updated messages degree,
      Executes (updateAndDecide core) (file [] [] (metadata [] leaders old messages degree [])) time
        (file [] (outputWord (some ⟨leaders,updated,decision core leaders updated⟩))
          (metadata ((Encoding.optional Encoding.natural).encode (decision core leaders updated))
            leaders old messages degree (Encoding.vista.encode updated))) := by
  unfold updateAndDecide
  let saved:=metadata [] leaders old messages degree []
  obtain ⟨a,ab,ar⟩:=prepareUpdate_executes leaders old messages degree
  obtain ⟨b,bb,br⟩:=ProtocolUpdate.complete_executes old messages degree valid received
  rw [success] at br
  have lifted:=lift_executes ProtocolUpdate.complete (by decide) _ _ saved b br
  change Executes updateCall (file (ProtocolUpdate.inputWord old messages degree) [] saved) b
    (file [] (true::Encoding.vista.encode updated) saved) at lifted
  have cr:=saveUpdated_executes leaders old updated messages degree
  obtain ⟨d,db,dr⟩:=decideAndReturn_executes core leaders old updated messages degree
    (updateVista_valid _ _ _ _ success) positive
  have consumed:Function.update (file [] (true::Encoding.vista.encode updated) saved) 1 (Encoding.vista.encode updated)=
      file [] (Encoding.vista.encode updated) saved := by
    funext r;by_cases one:r=1 <;> simp [file,one]
  have branch:=branch_executes_true (1:Fin 256) (useUpdated core) reject
    (file [] (true::Encoding.vista.encode updated) saved) _ (Encoding.vista.encode updated) _ rfl
    (by rw [consumed];unfold useUpdated;exact cr.sequence dr)
  exact ⟨_,by dsimp only [activeBudget,updateBudget];omega,ar.sequence (lifted.sequence branch)⟩

end Counting.StackMachine.ProtocolAdvance
