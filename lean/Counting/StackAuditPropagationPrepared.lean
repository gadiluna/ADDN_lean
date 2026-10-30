import Counting.StackAuditPropagationInput
import Counting.StackAuditPropagationAnchorStage
import Counting.StackAuditPropagationPrepareDown
import Counting.StackAuditPropagationDownStage
import Counting.AuditPropagationAssignedSize

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def propagationReadyFile (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : Store 42 :=
  Function.update (propagationSetupFile anchor vista values) 41 (List.replicate anchor true)

def propagationDoneFile (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : Store 42 :=
  fun i=>if i=1 then [true] else if i=17 then
    Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
    else if i=34 then Encoding.vista.encode vista
    else if i=35 then (Encoding.array Encoding.natural).encode (Executable.propagateWeights vista anchor values)
    else if i=36 then List.replicate vista.nodes.size true
    else if i=40 then List.replicate vista.nodes.size true else if i=42 then anchor.bits else []

abbrev propagatePrepared : Routine 42 := sequence anchorStage (sequence prepareDown downStage)

def preparedBudget (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : Nat :=
  let tableLength := (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length
  let zerosLength := ((Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0)).length
  let valuesLength := (Encoding.sequence Encoding.natural values.toList).length
  vista.nodes.size*(9000*(tableLength+zerosLength+valuesLength+anchor.size+vista.nodes.size+1)^4+2)+1+
    6*vista.nodes.size+valuesLength+6*anchor.size+6*anchor+16+
    (anchor*(downUniform vista tableLength
      (5*(((Encoding.array Encoding.natural).encode (assigned vista anchor values)).length+1)^3)+2)+1)+2

/-- Compose the exact anchor zip and all backward passes using their shared
serialized weight array. The vector may be short, excessive, or contain zero. -/
theorem propagatePrepared_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time ≤ preparedBudget anchor vista values,
      Executes propagatePrepared (propagationReadyFile anchor vista values) time
        (propagationDoneFile anchor vista values) := by
  let ready := propagationReadyFile anchor vista values
  have work (i : Fin 44) (small : i.val<17) (different : i≠1) : ready i=[] := by
    fin_cases i <;> simp_all [ready,propagationReadyFile,propagationSetupFile,propagationInputFile]
  obtain ⟨anchorTime,anchorBound,a⟩ := anchorStage_executes ready true [] rfl work rfl rfl rfl rfl
    vista anchor values rfl rfl rfl rfl rfl
  let anchored := anchorStageStore ready vista anchor values
  have b := prepareDown_executes anchored anchor vista.nodes.size
    (by simp [anchored,anchorStageStore])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile,propagationInputFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile,propagationInputFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile,propagationInputFile])
    (by simp [anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile,propagationInputFile])
  let prepared := downSetupStore anchored anchor vista.nodes.size
  have preparedWork (i : Fin 44) (small : i.val<17) (different : i≠1) : prepared i=[] := by
    fin_cases i <;> simp_all [prepared,downSetupStore,anchored,anchorStageStore,
      ready,propagationReadyFile,propagationSetupFile,propagationInputFile]
  have empty (i : Fin 44) (member : i∈([18,19,20,21,23,24,25,26,30,31,32,33,37,38] : List (Fin 44))) :
      prepared i=[] := by
    fin_cases i <;> simp_all [prepared,downSetupStore,anchored,anchorStageStore,
      ready,propagationReadyFile,propagationSetupFile,propagationInputFile]
  obtain ⟨downTime,downBound,c⟩ := downStage_executes prepared true []
    (by simp [prepared,downSetupStore,anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile])
    preparedWork empty vista (assigned vista anchor values)
    (by simp only [assigned,Executable.assignEntries_size,Array.size_replicate])
    (by simp [prepared,downSetupStore,anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile,propagationInputFile])
    (by simp [prepared,downSetupStore,anchored,anchorStageStore,ready,propagationReadyFile,propagationSetupFile])
    (by simp [prepared,downSetupStore,anchored,anchorStageStore])
    (by simp [prepared,downSetupStore]) anchor (by simp [prepared,downSetupStore])
    (by simp [prepared,downSetupStore]) fits
  have result : downStageStore prepared vista anchor (assigned vista anchor values)=
      propagationDoneFile anchor vista values := by
    funext i
    fin_cases i <;> simp [downStageStore,prepared,downSetupStore,anchored,anchorStageStore,
      ready,propagationReadyFile,propagationSetupFile,propagationInputFile,propagationDoneFile,
      Executable.propagateWeights_eq_fold,assigned]
  rw [result] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have rest := remainingValues_encoded_length anchor vista.nodes.toList values.toList
  have countSource : ready 17=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom := rfl
  have zeroSource : ready 35=(Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0) := rfl
  have valueSource : ready 36=Encoding.sequence Encoding.natural values.toList := rfl
  have sameTable : prepared 17=ready 17 := by simp [prepared,downSetupStore,anchored,anchorStageStore]
  have remainder : anchored 36=Encoding.sequence Encoding.natural (remainingValues anchor vista.nodes.toList values.toList) := by
    simp [anchored,anchorStageStore]
  rw [countSource,zeroSource,valueSource] at anchorBound
  rw [sameTable,countSource] at downBound
  rw [remainder]
  dsimp only [preparedBudget]
  omega

end Counting.StackMachine.AuditPropagation
