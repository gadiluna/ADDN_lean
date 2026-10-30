import Counting.RealizabilityVerifier

namespace Counting.RealizabilityVerifier
open Executable

theorem filtered_sum_scan {α : Type} (values : List α) (predicate : α → Bool) (value : α → Nat) :
    ((values.filter predicate).map value).sum=
      (values.map (fun a => if predicate a then value a else 0)).sum := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    cases accepted : predicate head <;> simp [accepted,ih]

/-- The implementation may scan every stored node without constructing a
filtered level list. This identity also holds on malformed views or counts. -/
theorem initialCount_scan (vista : Vista) (weights : Array Nat) (b : Bool) :
    initialCount vista weights b=
      ((List.range vista.nodes.size).map (fun i =>
        if (vista.node i).level=0 ∧ (vista.node i).leader=b then weight weights i else 0)).sum := by
  rw [initialCount,levelNodes,filtered_sum_scan]
  congr 1
  apply List.map_congr_left
  intro i _member
  by_cases level : (vista.node i).level=0 <;>
    by_cases leader : (vista.node i).leader=b <;> simp [level,leader]

theorem childCount_scan (vista : Vista) (weights : Array Nat) (r old : Nat) :
    childCount vista weights r old=
      ((List.range vista.nodes.size).map (fun i =>
        if (vista.node i).level=r+1 ∧ (vista.node i).parent=some old then weight weights i else 0)).sum := by
  rw [childCount,children,levelNodes,filtered_sum_scan,filtered_sum_scan]
  congr 1
  apply List.map_congr_left
  intro i _member
  by_cases level : (vista.node i).level=r+1 <;>
    by_cases parent : (vista.node i).parent=some old <;> simp [level,parent]

theorem supply_scan (vista : Vista) (weights : Array Nat) (r old : Nat) :
    supply vista weights r old=
      ((List.range vista.nodes.size).map (fun i =>
        if (vista.node i).level=r+1 ∧ (vista.node i).parent=some old
        then weight weights i*(vista.node i).degree else 0)).sum := by
  rw [supply,children,levelNodes,filtered_sum_scan,filtered_sum_scan]
  congr 1
  apply List.map_congr_left
  intro i _member
  by_cases level : (vista.node i).level=r+1 <;>
    by_cases parent : (vista.node i).parent=some old <;> simp [level,parent]

theorem demand_scan (vista : Vista) (weights : Array Nat) (r old : Nat) :
    demand vista weights r old=
      ((List.range vista.nodes.size).map (fun i =>
        if (vista.node i).level=r+1 then weight weights i*countFrom (vista.node i) old else 0)).sum := by
  rw [demand,levelNodes,filtered_sum_scan]
  simp only [beq_iff_eq]

theorem hidden_scan (N : Nat) (vista : Vista) (weights : Array Nat) (r : Nat) :
    hidden N vista weights r=N-
      ((List.range vista.nodes.size).map (fun i =>
        if (vista.node i).level=r+1 then weight weights i else 0)).sum := by
  rw [hidden,levelNodes,filtered_sum_scan]
  simp only [beq_iff_eq]

end Counting.RealizabilityVerifier
