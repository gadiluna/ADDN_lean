import Counting.NetworkRecognitionBitGraph
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn

namespace Counting.Encoding

/-- The semantic leader cardinality is the literal count obtained by
scanning the explicit Boolean leader array. -/
theorem inputLeaderCount_eq_count (input : Simulation.Input) :
    inputLeaderCount input=input.leaders.toList.count true := by
  let leaders : List.Vector Bool input.leaders.size:=⟨input.leaders.toList,by simp⟩
  simpa [inputLeaderCount,inputLeader,leaders,List.Vector.get] using
    Fin.card_filter_univ_eq_vector_get_eq_count true leaders

end Counting.Encoding

namespace Counting.StackMachine.NetworkRecognition
open RealizabilityVerifier

private theorem matrixBits_rows (n : Nat) (graph : Simulation.RoundGraph) :
    matrixBits n graph=(List.ofFn (fun i:Fin n=>List.ofFn
      (fun j:Fin n=>decide (0<Encoding.matrixEdge graph n i j)))).flatten := by
  rw [matrixBits,CompactGraph.matrixBits,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have encoded : (⟨i.val*n+j.val,by have := i.isLt;have := j.isLt;nlinarith⟩ : Fin (n*n))=
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [encoded,Equiv.symm_apply_apply]

private theorem row_positivity_ofFn (row : Array Nat) (n : Nat) (shape : row.size=n) :
    row.toList.map (fun a=>decide (0<a))=
      List.ofFn (fun j:Fin n=>decide (0<row[j.val]?.getD 0)) := by
  subst n
  rw [←List.ofFn_getElem_eq_map]
  simp only [Array.length_toList]
  apply congrArg List.ofFn
  funext j
  simp

/-- Flattening the positive entries of the actual, shape-checked matrix
produces exactly the row-major bit graph consumed by the verified BFS. -/
theorem matrix_positivity_eq_bits (n : Nat) (graph : Simulation.RoundGraph)
    (shape : Encoding.matrixShape n graph=true) :
    graph.toList.flatMap (fun row=>row.toList.map (fun a=>decide (0<a)))=matrixBits n graph := by
  simp only [Encoding.matrixShape,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true] at shape
  obtain ⟨dimension,rows⟩:=shape
  subst n
  rw [matrixBits_rows,List.flatMap_def,←List.ofFn_getElem_eq_map]
  simp only [Array.length_toList]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [row_positivity_ofFn _ graph.size (by simpa using rows i.val i.isLt)]
  apply congrArg List.ofFn
  funext j
  simp [Encoding.matrixEdge]

/-- The exact physically produced bit word therefore has the same
strong-connectivity decision as the explicit network matrix. -/
theorem matrix_positivity_check (n : Nat) (graph : Simulation.RoundGraph)
    (shape : Encoding.matrixShape n graph=true) :
    BitGraph.check n (graph.toList.flatMap (fun row=>row.toList.map (fun a=>decide (0<a))))
        (List.replicate n true)=
      DirectedCounting.strongConnectivityCheck
        (fun source target:Fin n=>decide (0<Encoding.matrixEdge graph n source target)) := by
  rw [matrix_positivity_eq_bits n graph shape,matrixBits_check]

end Counting.StackMachine.NetworkRecognition
