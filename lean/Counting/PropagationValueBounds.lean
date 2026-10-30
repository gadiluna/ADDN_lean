import Counting.ExecutableRefinementWeights
import Counting.EncodingArrayUpdateBounds
import Mathlib.Data.Nat.Size

namespace Counting.Executable

/-- The number of summands in any backward equation is bounded by the
stored DAG, independently of the binary weights. -/
theorem children_length_le_size (vista : Vista) (parent level : Nat) :
    (children vista parent level).length ≤ vista.nodes.size := by
  apply (List.length_filter_le _ _).trans
  simpa only [levelNodes,List.length_range] using
    List.length_filter_le (fun i=>(vista.node i).level==level) (List.range vista.nodes.size)

private theorem bounded_map_sum (indices : List Nat) (value : Nat→Nat) (bound : Nat)
    (bounded : ∀ i∈indices,value i ≤ bound) :
    (indices.map value).sum ≤ indices.length*bound := by
  induction indices with
  | nil=>simp
  | cons i rest ih=>
    have first:=bounded i (by simp)
    have tail:=ih (fun j member=>bounded j (by simp [member]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [first,tail]

/-- This bound also applies during a partially completed level. Writes at
that level do not feed back into the next-level children used by the scan. -/
theorem updateNodes_value_bound (vista : Vista) (r : Nat) (nodes : List Nat) (weights : Array Nat)
    (size : weights.size=vista.nodes.size) (distinct : nodes.Nodup)
    (atLevel : ∀ i∈nodes,i∈levelNodes vista r) (M : Nat)
    (bounded : ∀ i : Nat,(weights[i]?.getD 0) ≤ M) (index : Nat) :
    (updateNodes vista r nodes weights)[index]?.getD 0 ≤ M*(vista.nodes.size+1) := by
  by_cases present : index∈nodes
  · rw [updateNodes_entry vista r nodes weights size distinct atLevel index present]
    have summands:=bounded_map_sum (children vista index (r+1)) (fun i=>weights[i]?.getD 0) M
      (fun i _=>bounded i)
    have count:=children_length_le_size vista index (r+1)
    have scaled:=Nat.mul_le_mul_right M count
    nlinarith only [summands,scaled,Nat.zero_le M]
  · rw [updateNodes_unchanged vista r nodes weights index present]
    have old:=bounded index
    nlinarith only [old,Nat.zero_le (M*vista.nodes.size)]

theorem propagateLevel_value_bound (vista : Vista) (weights : Array Nat) (r M : Nat)
    (size : weights.size=vista.nodes.size) (bounded : ∀ i : Nat,(weights[i]?.getD 0) ≤ M) (index : Nat) :
    (propagateLevel vista weights r)[index]?.getD 0 ≤ M*(vista.nodes.size+1) :=
  updateNodes_value_bound vista r (levelNodes vista r) weights size (levelNodes_nodup vista r)
    (fun _ member=>member) M bounded index

theorem propagateDown_value_bound (vista : Vista) (weights : Array Nat) (rounds M : Nat)
    (size : weights.size=vista.nodes.size) (bounded : ∀ i : Nat,(weights[i]?.getD 0) ≤ M) (index : Nat) :
    (propagateDown vista rounds weights)[index]?.getD 0 ≤ M*(vista.nodes.size+1)^rounds := by
  induction rounds generalizing weights M with
  | zero=>simpa [propagateDown] using bounded index
  | succ rounds ih=>
    rw [propagateDown_succ]
    have next:=ih (propagateLevel vista weights rounds) (M*(vista.nodes.size+1))
      ((propagateLevel_size vista rounds weights).trans size)
      (propagateLevel_value_bound vista weights rounds M size bounded)
    convert next using 1
    ring

/-- Numeric growth across levels is exponential at worst, but its binary
length grows only additively in the explicit number of levels. -/
theorem propagateDown_size_bound (vista : Vista) (weights : Array Nat) (rounds M : Nat)
    (size : weights.size=vista.nodes.size) (bounded : ∀ i : Nat,(weights[i]?.getD 0) ≤ M) (index : Nat) :
    ((propagateDown vista rounds weights)[index]?.getD 0).size ≤
      M.size+rounds*(vista.nodes.size+1).size := by
  have value:=propagateDown_value_bound vista weights rounds M size bounded index
  have positive : 0<(vista.nodes.size+1)^rounds := pow_pos (by omega) _
  have power : (vista.nodes.size+1)^rounds ≤ (2^(vista.nodes.size+1).size)^rounds :=
    Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self (vista.nodes.size+1))) _
  have high : M*(vista.nodes.size+1)^rounds < 2^(M.size+rounds*(vista.nodes.size+1).size) := by
    calc
      _ < 2^M.size*(vista.nodes.size+1)^rounds := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self M) positive
      _ ≤ 2^M.size*(2^(vista.nodes.size+1).size)^rounds := Nat.mul_le_mul_left _ power
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring
  exact Nat.size_le.mpr (value.trans_lt high)

end Counting.Executable
