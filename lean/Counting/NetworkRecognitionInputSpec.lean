import Counting.NetworkRecognitionMatrixSpec
import Counting.NetworkRecognitionLeaderCheck
import Counting.NetworkRecognitionRoundsHeader

namespace Counting.StackMachine.NetworkRecognition
set_option backward.isDefEq.respectTransparency false

def networkGraphs (input:Simulation.Input) : List (List (List Nat)) := input.rounds.toList.map matrixRows

theorem networkGraphs_encoded (input:Simulation.Input) :
    (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode (networkGraphs input)=
      (Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds := by
  change Encoding.natural.encode (networkGraphs input).length++
    Encoding.sequence (Encoding.list (Encoding.list Encoding.natural)) (networkGraphs input)=
    Encoding.natural.encode input.rounds.toList.length++
      Encoding.sequence (Encoding.array (Encoding.array Encoding.natural)) input.rounds.toList
  simp only [networkGraphs,List.length_map]
  rw [sequence_map_codec (Encoding.array (Encoding.array Encoding.natural))
    (Encoding.list (Encoding.list Encoding.natural)) matrixRows matrixRows_encoded]

theorem networkInput_encoded (input:Simulation.Input) :
    Encoding.networkInput.encode input=
      (Encoding.list Encoding.boolean).encode input.leaders.toList++
        (Encoding.list (Encoding.list (Encoding.list Encoding.natural))).encode (networkGraphs input) := by
  rw [networkGraphs_encoded]
  rfl

theorem all_array_fin {A:Type} (values:Array A) (predicate:A→Bool) :
    values.toList.all predicate=(List.finRange values.size).all (fun i=>predicate values[i.val]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_finRange,true_implies]
  constructor
  · intro all i
    exact all values[i.val] (by simp)
  · intro all value member
    obtain ⟨i,inside,equal⟩:=Array.mem_iff_getElem.mp (by simpa using member)
    subst value
    exact all ⟨i,inside⟩

theorem networkGraphs_decisions (input:Simulation.Input) :
    roundDecisions input.leaders.size (networkGraphs input)=
      (List.finRange input.rounds.size).all (fun i=>
        Encoding.matrixShape input.leaders.size input.rounds[i.val] &&
          DirectedCounting.strongConnectivityCheck
            (fun source target:Fin input.leaders.size=>decide (0<Encoding.matrixEdge input.rounds[i.val] input.leaders.size source target))) := by
  simp only [roundDecisions,networkGraphs,List.all_map,Function.comp_def]
  simp_rw [matrixAccepted_actual]
  exact all_array_fin _ _

theorem network_decisions_actual (input:Simulation.Input) :
    (leadersAccepted input.leaders.toList && roundDecisions input.leaders.toList.length (networkGraphs input))=
      Encoding.networkValid input := by
  rw [Array.length_toList,networkGraphs_decisions]
  simp only [leadersAccepted,Array.length_toList,Encoding.networkValid,Encoding.inputLeaderCount_eq_count]

end Counting.StackMachine.NetworkRecognition
