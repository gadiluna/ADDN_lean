import Counting.NetworkVistaReceiverRead
import Counting.NetworkVistaDegreeActual
import Counting.NetworkVistaCollectActual

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def degreeRoles : Fin 22 ↪ Fin 130 where
  toFun i := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,111,20,109] i
  inj' := by decide

def ownDegree : Routine 128 := relocate rowTotal degreeRoles

theorem ownDegree_executes (data : Fin 30→List Bool) (row : Array Nat)
    (source : data 9=(Encoding.array Encoding.natural).encode row) (e11 : data 11=[]) :
    ∃ time ≤ 2100*((data 9).length+1)^3,
      Executes ownDegree (file data) time (file (Function.update data 11 row.toList.sum.bits)) := by
  let localStore := file data ∘ degreeRoles
  obtain ⟨time,bound,run⟩ := rowTotal_executes localStore row (by simp [localStore,degreeRoles,file,source])
    (by intro r different;fin_cases r <;> simp_all [localStore,degreeRoles,file])
  have inputAt : localStore 21=data 9 := by simp [localStore,degreeRoles,file]
  rw [inputAt] at bound
  have wide := relocate_executes rowTotal degreeRoles (file data) time _ run
  rw [relocatedStore_update,relocatedStore_original] at wide
  change Executes ownDegree (file data) time (Function.update (file data) (context 11) row.toList.sum.bits) at wide
  rw [file_update] at wide
  exact ⟨time,bound,wide⟩

def collectRoles : Fin 40 ↪ Fin 130 where
  toFun i := ![0,115,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,104,24,25,26,112,
    28,29,30,31,32,33,34,35,36,102,103,39] i
  inj' := by decide

def incoming : Routine 128 := relocate collectPreserving collectRoles

theorem incoming_executes (data : Fin 30→List Bool) (n : Nat)
    (graph : Simulation.RoundGraph) (views : Fin n→Executable.Vista) (receiver : Fin n)
    (status : data 15=[true]) (e12 : data 12=[])
    (shape : Encoding.matrixShape n graph=true)
    (viewInput : data 2=(Encoding.array Encoding.vista).encode (Array.ofFn views))
    (rowInput : data 3=(Encoding.array (Encoding.array Encoding.natural)).encode graph)
    (position : (data 4).length=receiver.val) :
    ∃ time ≤ Complexity.polynomial 26000 5 ((data 2).length+(data 3).length+(data 4).length+n),
      Executes incoming (file data) time (file (Function.update data 12
        ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
          (Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver)))) := by
  let localStore := file data ∘ collectRoles
  have empty : SenderEmpty localStore := by
    constructor
    · intro r small different
      fin_cases r <;> simp_all [localStore,collectRoles,file]
    · intro r low high
      fin_cases r <;> simp_all [localStore,collectRoles,file]
  obtain ⟨time,bound,run⟩ := collectPreserving_actual localStore true []
    (by simp [localStore,collectRoles,file,status]) empty
    (by simp [localStore,collectRoles,file]) (by simp [localStore,collectRoles,file])
    (by simp [localStore,collectRoles,file]) (by simp [localStore,collectRoles,file])
    (by simp [localStore,collectRoles,file]) n graph views receiver shape
    (by simp [localStore,collectRoles,file,viewInput]) (by simp [localStore,collectRoles,file,rowInput])
    (by simpa [localStore,collectRoles,file] using position)
  have s37 : localStore 37=data 2 := by simp [localStore,collectRoles,file]
  have s38 : localStore 38=data 3 := by simp [localStore,collectRoles,file]
  have s23 : localStore 23=data 4 := by simp [localStore,collectRoles,file]
  rw [s37,s38,s23] at bound
  have wide := relocate_executes collectPreserving collectRoles (file data) time _ run
  rw [relocatedStore_update,relocatedStore_original] at wide
  change Executes incoming (file data) time (Function.update (file data) (context 12) _) at wide
  rw [file_update] at wide
  exact ⟨time,bound,wide⟩

end Counting.StackMachine.NetworkVista.Receiver
