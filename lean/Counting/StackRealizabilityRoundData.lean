import Counting.StackRealizabilityRoundMasks
import Counting.StackRealizabilityRoundPoint
import Counting.StackRealizabilityRoundOutside
import Counting.StackRealizabilityRoundIncidences
import Counting.StackRealizabilityRoundGraph

namespace Counting.StackMachine.RealizabilityCheck
open Routine

/-- Persistent inputs and outer-loop state; all round work starts empty. -/
def roundInputData (nodes : List Executable.Node) (values : List Nat) (order round : Nat)
    (status : List Bool) (extra : Fin 3→List Bool) : Fin 20→List Bool := fun r =>
  if r=0 then (Encoding.list Encoding.node).encode nodes else
  if r=1 then (Encoding.list Encoding.natural).encode values else
  if r=2 then order.bits else if r=3 then round.bits else if r=5 then status else
  if large : 17≤r.val then extra ⟨r.val-17,by omega⟩ else []

def roundVisibleValue (nodes : List Executable.Node) (values : List Nat) (round : Nat) : Nat :=
  levelRangeSum nodes (round+1) 0 values

def roundNumericValue (nodes : List Executable.Node) (values : List Nat) (order round : Nat) : Bool :=
  pointRangeCheck nodes values (nodes.map (fun node=>decide (node.level=round))++[false])
    (round+1) order (roundVisibleValue nodes values round) 0 (nodes.length+1)

def roundComputedTables (nodes : List Executable.Node) (values : List Nat) (order round : Nat) : Fin 8→List Bool := ![
  nodes.map (fun node=>decide (node.level=round+1))++[false],
  nodes.map (fun node=>decide (node.level=round))++[false],
  List.replicate nodes.length false++[decide (0<order-roundVisibleValue nodes values round)],
  nodes.map (fun node=>decide (0<node.degree))++[false],
  leavingRangeValues nodes values (round+1) 0 (nodes.length+1),
  deficitRangeValues nodes values (round+1) 0 (nodes.length+1),
  parentMatrixValues nodes,incomingMatrixValues nodes]

def roundComputedCheck (nodes : List Executable.Node) (values : List Nat) (order round : Nat) : Bool :=
  roundNumericValue nodes values order round &&
    (if 1<order then graphFieldsAnswer (roundComputedTables nodes values order round) (nodes.length+1) else true)

def roundComputedData (nodes : List Executable.Node) (values : List Nat) (order round : Nat)
    (status : List Bool) (extra : Fin 3→List Bool) : Fin 20→List Bool := fun r =>
  if r=4 then (round+1).bits else if r=6 then Encoding.sequence Encoding.node nodes else
  if r=7 then List.replicate (nodes.length+1) true else
  if r=8 then roundComputedTables nodes values order round 1 else
  if r=9 then roundComputedTables nodes values order round 0 else
  if r=10 then roundComputedTables nodes values order round 3 else
  if r=11 then roundComputedTables nodes values order round 4 else
  if r=12 then roundComputedTables nodes values order round 5 else
  if r=13 then roundComputedTables nodes values order round 2 else
  if r=14 then roundComputedTables nodes values order round 6 else
  if r=15 then roundComputedTables nodes values order round 7 else
  if r=16 then (roundVisibleValue nodes values round).bits else
    roundInputData nodes values order round status extra r

end Counting.StackMachine.RealizabilityCheck
