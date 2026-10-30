import Counting.StackRealizabilityPointBody

namespace Counting.StackMachine.RealizabilityCheck

def leavingRangeValues (nodes : List Executable.Node) (values : List Nat) (target start : Nat) : Nat→List Bool
  | 0 => []
  | count+1 => decide (0<values[start]?.getD 0-childRangeSum nodes target start 0 values)::
      leavingRangeValues nodes values target (start+1) count

def deficitRangeValues (nodes : List Executable.Node) (values : List Nat) (target start : Nat) : Nat→List Bool
  | 0 => []
  | count+1 => decide (demandRangeSum nodes target start 0 values<supplyRangeSum nodes target start 0 values)::
      deficitRangeValues nodes values target (start+1) count

def pointRangeCheck (nodes : List Executable.Node) (values : List Nat) (masks : List Bool)
    (target order visible start : Nat) : Nat→Bool
  | 0 => true
  | count+1 =>
    (if RealizabilityVerifier.BitGraph.bitAt masks start then
      roundBoundsCheck (childRangeSum nodes target start 0 values) (values[start]?.getD 0)
        (supplyRangeSum nodes target start 0 values) (demandRangeSum nodes target start 0 values) visible order
      else true) && pointRangeCheck nodes values masks target order visible (start+1) count

@[simp] theorem leavingRangeValues_length (nodes : List Executable.Node) (values : List Nat)
    (target start count : Nat) : (leavingRangeValues nodes values target start count).length=count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [leavingRangeValues,ih]

@[simp] theorem deficitRangeValues_length (nodes : List Executable.Node) (values : List Nat)
    (target start count : Nat) : (deficitRangeValues nodes values target start count).length=count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [deficitRangeValues,ih]

end Counting.StackMachine.RealizabilityCheck
