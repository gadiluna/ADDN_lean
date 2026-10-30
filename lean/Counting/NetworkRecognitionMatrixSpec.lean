import Counting.NetworkRecognitionMatrixCheck

namespace Counting.StackMachine.NetworkRecognition
set_option backward.isDefEq.respectTransparency false

def matrixRows (graph:Simulation.RoundGraph) : List (List Nat) := graph.toList.map Array.toList

theorem sequence_map_codec {A B:Type} (first:Encoding.Codec A) (second:Encoding.Codec B)
    (f:A→B) (equal:∀a,second.encode (f a)=first.encode a) (values:List A) :
    Encoding.sequence second (values.map f)=Encoding.sequence first values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.map_cons,Encoding.sequence,equal,ih]

theorem matrixRows_encoded (graph:Simulation.RoundGraph) :
    (Encoding.list (Encoding.list Encoding.natural)).encode (matrixRows graph)=
      (Encoding.array (Encoding.array Encoding.natural)).encode graph := by
  change Encoding.natural.encode (matrixRows graph).length++
    Encoding.sequence (Encoding.list Encoding.natural) (matrixRows graph)=
    Encoding.natural.encode graph.toList.length++Encoding.sequence (Encoding.array Encoding.natural) graph.toList
  simp only [matrixRows,List.length_map]
  rw [sequence_map_codec (Encoding.array Encoding.natural) (Encoding.list Encoding.natural) Array.toList (by intro row;rfl)]

theorem matrixRows_shape (width:Nat) (graph:Simulation.RoundGraph) :
    matrixShape width (matrixRows graph)=Encoding.matrixShape width graph := by
  apply Bool.eq_iff_iff.mpr
  simp only [matrixShape,rowLengths,matrixRows,Encoding.matrixShape,Bool.and_eq_true,decide_eq_true_eq,
    List.length_map,Array.length_toList,beq_iff_eq,List.all_map,List.all_eq_true,Array.all_eq_true]
  constructor
  · rintro ⟨dimension,rows⟩
    refine ⟨dimension.symm,?_⟩
    intro i inside
    have row:=rows graph[i] (by simp)
    have shape:width=graph[i].size:=by simpa only [Function.comp_apply,Array.length_toList,decide_eq_true_eq] using row
    exact shape.symm
  · rintro ⟨dimension,rows⟩
    refine ⟨dimension.symm,?_⟩
    intro row member
    obtain ⟨i,inside,equal⟩:=Array.mem_iff_getElem.mp (by simpa using member)
    subst row
    simpa only [Function.comp_apply,Array.length_toList,decide_eq_true_eq] using (rows i inside).symm

theorem matrixRows_bits (graph:Simulation.RoundGraph) :
    adjacencyBits (matrixRows graph)=graph.toList.flatMap (fun row=>row.toList.map (fun a=>decide (0<a))) := by
  simp only [adjacencyBits,matrixRows,List.flatMap_map]

theorem matrixAccepted_actual (width:Nat) (graph:Simulation.RoundGraph) :
    matrixAccepted width (matrixRows graph)=
      (Encoding.matrixShape width graph && DirectedCounting.strongConnectivityCheck
        (fun source target:Fin width=>decide (0<Encoding.matrixEdge graph width source target))) := by
  rw [matrixAccepted,matrixRows_shape]
  cases shape:Encoding.matrixShape width graph with
  | false => simp
  | true =>
    simp only [Bool.true_and]
    rw [matrixRows_bits,matrix_positivity_eq_bits width graph shape,matrixBits_edge]

end Counting.StackMachine.NetworkRecognition
