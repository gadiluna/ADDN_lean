import Counting.StackRealizabilityCallFile
import Counting.StackEncodingListReadHeader
import Counting.StackEmitNatural
import Counting.EncodingNetwork

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def initialRoundRoles : FullListWorkspace 113 :=
  ⟨![120,104,0,1,121,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def initialRoundHeader : Routine 128 := readListHeader 113 initialRoundRoles

def initialRoundData (data : Fin 30→List Bool) (rounds : Array Simulation.RoundGraph) : Fin 30→List Bool :=
  Function.update (Function.update data 20
    (Encoding.sequence (Encoding.array (Encoding.array Encoding.natural)) rounds.toList))
    21 (List.replicate rounds.size true)

theorem initialRoundHeader_executes (data : Fin 30→List Bool) (rounds : Array Simulation.RoundGraph)
    (encoded : data 20=(Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode rounds)
    (flag : data 4=[true]) (empty : data 21=[]) :
    ∃ time ≤ 1820*((data 20).length+1)^3,
      Executes initialRoundHeader (file data) time (file (initialRoundData data rounds)) := by
  obtain ⟨time,bound,run⟩ := readListHeader_canonical 113 initialRoundRoles (file data) true []
    (by simp [initialRoundRoles,flag,file])
    (by
      intro i mem
      fin_cases i <;> simp_all [initialRoundRoles,file])
    (Encoding.array (Encoding.array Encoding.natural))
    (Encoding.array_length_positive (Encoding.array Encoding.natural)) rounds.toList []
    (by simp [initialRoundRoles,file,encoded,Encoding.array,Encoding.transport])
  have src : file data (initialRoundRoles 0)=data 20 := by rfl
  rw [src] at bound
  have output : Function.update (Function.update (file data) (initialRoundRoles 0)
      (Encoding.sequence (Encoding.array (Encoding.array Encoding.natural)) rounds.toList++[]))
      (initialRoundRoles 4) (List.replicate rounds.toList.length true)=file (initialRoundData data rounds) := by
    change Function.update (Function.update (file data) (context 20) _) (context 21) _=_
    simp only [List.append_nil,Array.length_toList,file_update,initialRoundData]
  rw [output] at run
  exact ⟨time,bound,run⟩

def initialPopulationRoles : PowerWorkspace 125 := ⟨![122,123,0,1,2],by decide⟩

def initialPopulation : Routine 128 := emitNatural 125 initialPopulationRoles

theorem initialPopulation_executes (data : Fin 30→List Bool) (empty : data 23=[]) :
    ∃ time ≤ 20*((data 22).length+1)^2,
      Executes initialPopulation (file data) time
        (file (Function.update data 23 (Encoding.natural.encode (data 22).length))) := by
  obtain ⟨time,bound,run⟩ := emitNatural_executes 125 initialPopulationRoles (file data)
    (by simp [initialPopulationRoles,file]) (by simp [initialPopulationRoles,file])
    (by simp [initialPopulationRoles,file])
  change time≤20*((data 22).length+1)^2 at bound
  change Executes initialPopulation (file data) time
    (Function.update (file data) (context 23) (Encoding.natural.encode (data 22).length++data 23)) at run
  rw [empty,List.append_nil,file_update] at run
  exact ⟨time,bound,run⟩

end Counting.StackMachine.NetworkVista.Run
