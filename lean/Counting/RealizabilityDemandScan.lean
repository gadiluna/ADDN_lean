import Counting.DagSemanticsLabels
import Counting.RealizabilityInitialCountScan

namespace Counting.RealizabilityVerifier
open Counting.Executable

theorem bundleCount_sum (edges : List (Nat × Nat)) (source : Nat) :
    bundleCount source edges = (edges.map (fun edge => if edge.1=source then edge.2 else 0)).sum := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => simp only [bundleCount,List.map_cons,List.sum_cons,ih]

/-- Canonical incoming lists contain each source at most once. A bounded
scan can therefore replace first-match lookup by a binary sum. -/
theorem countFrom_sum (node : Node) (source : Nat) (sorted : countsSorted node.incoming=true) :
    countFrom node source = (node.incoming.map (fun edge => if edge.1=source then edge.2 else 0)).sum := by
  rw [countFrom,lookup_eq_bundleCount _ (sparse_of_countsSorted _ sorted),bundleCount_sum]

theorem weighted_countFrom_sum (node : Node) (source amount : Nat) (sorted : countsSorted node.incoming=true) :
    amount*countFrom node source =
      (node.incoming.map (fun edge => if edge.1=source then amount*edge.2 else 0)).sum := by
  rw [countFrom_sum node source sorted]
  have scaled (edges : List (Nat × Nat)) :
      amount*(edges.map (fun edge => if edge.1=source then edge.2 else 0)).sum =
        (edges.map (fun edge => if edge.1=source then amount*edge.2 else 0)).sum := by
    induction edges with
    | nil => simp
    | cons edge rest ih =>
      simp only [List.map_cons,List.sum_cons,Nat.mul_add,ih]
      by_cases same : edge.1=source <;> simp [same]
  exact scaled node.incoming

end Counting.RealizabilityVerifier
