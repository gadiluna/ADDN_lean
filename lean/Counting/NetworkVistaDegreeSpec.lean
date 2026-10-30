import Counting.EncodingNetworkSemantics
import Mathlib.Algebra.BigOperators.Fin

namespace Counting.Encoding

/-- Summing an explicit row agrees with the finite-agent sum once its
length has been checked; binary multiplicities may be zero or arbitrary. -/
theorem row_sum_fin (row : Array Nat) (n : Nat) (shape : row.size=n) :
    row.toList.sum=∑ b : Fin n,row[b.val]?.getD 0 := by
  subst n
  have result:=Fin.sum_univ_getElem row.toList
  simpa using result.symm

theorem matrix_row_sum (n : Nat) (graph : Simulation.RoundGraph)
    (shape : matrixShape n graph=true) (a : Fin n) :
    (graph[a.val]?.getD #[]).toList.sum=∑ b : Fin n,matrixEdge graph n a b := by
  simp only [matrixShape,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true] at shape
  obtain ⟨dimension,rows⟩:=shape
  have inside : a.val<graph.size := by have:=a.isLt;omega
  have rowShape : (graph[a.val]?.getD #[]).size=n := by
    simpa only [Array.getElem?_eq_getElem inside,Option.getD_some] using rows a.val inside
  exact row_sum_fin (graph[a.val]?.getD #[]) n rowShape

end Counting.Encoding
