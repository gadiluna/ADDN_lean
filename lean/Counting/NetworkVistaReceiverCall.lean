import Counting.StackVistaRawPolynomial
import Counting.StackRealizabilityCallFile
import Counting.StackRegisterFrames

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 200000

def rawCallRoles : Fin 96 ↪ Fin 130 where
  toFun i := ![113,107,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] i
  inj' := by decide

def rawCall : Routine 128 := relocate DagUpdate.Raw.complete rawCallRoles

theorem rawCall_executes (data : Fin 30→List Bool) (round degree : Nat) (leader : Bool)
    (old : Executable.Vista) (messages : List (Executable.Vista×Nat))
    (input : data 13=DagUpdate.Raw.inputWord round leader degree old messages) (vacant : data 7=[]) :
    ∃ time ≤ Complexity.polynomial DagUpdate.Raw.completeCoefficient 61
        (DagUpdate.Raw.inputWord round leader degree old messages).length,
      Executes rawCall (file data) time
        (file (Function.update (Function.update data 13 []) 7
          (Encoding.vista.encode (DagUpdate.Raw.updated round leader degree old messages)))) := by
  obtain ⟨time,bound,run⟩ := DagUpdate.Raw.complete_polynomial round leader degree old messages
  have initial : file data ∘ rawCallRoles=inputStore 94 (DagUpdate.Raw.inputWord round leader degree old messages) := by
    funext r
    fin_cases r <;> simp [rawCallRoles,inputStore,file,input,vacant]
  rw [←initial] at run
  have output : outputStore 94 (Encoding.vista.encode (DagUpdate.Raw.updated round leader degree old messages))=
      Function.update (Function.update (file data ∘ rawCallRoles) 0 []) 1
        (Encoding.vista.encode (DagUpdate.Raw.updated round leader degree old messages)) := by
    rw [initial]
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> simp [outputStore,inputStore,r0,r1]
  rw [output] at run
  have wide := relocate_executes DagUpdate.Raw.complete rawCallRoles (file data) time _ run
  rw [relocatedStore_update,relocatedStore_update,relocatedStore_original] at wide
  have at0 : rawCallRoles 0=context 13 := by simp [rawCallRoles,context]
  have at1 : rawCallRoles 1=context 7 := by simp [rawCallRoles,context]
  rw [at0,at1,file_update,file_update] at wide
  exact ⟨time,bound,wide⟩

end Counting.StackMachine.NetworkVista.Receiver
