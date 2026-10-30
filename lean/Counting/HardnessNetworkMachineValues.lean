import Counting.HardnessNetworkMachineRows

namespace Counting.HardnessNetworkMachine

/-- The explicit population represented by the coefficient table. -/
def networkOrder (base : Nat) (coefficients : List Nat) : Nat :=
  2+coefficients.length*base

/-- The baseline group has one extra member; all remaining groups have
exactly `base` members. The initial zero is the leader's self-loop entry. -/
def leaderRow (base : Nat) (coefficients : List Nat) : List Nat :=
  0::(List.replicate (base+1) (coefficients.headD 0)++
    coefficients.tail.flatMap (List.replicate base))

/-- Consecutive nonleaders forward to the next member, and the final member
of the group forwards to the unique leader, at column zero. -/
def groupRows (width start size : Nat) : List (List Nat) :=
  consecutiveRows width (start+1) (size-1)++[oneHotRow width 0]

def ordinaryGroupRows (width start size count : Nat) : List (List Nat) :=
  (List.range count).flatMap (fun j=>groupRows width (start+j*size) size)

def pathMatrix (base : Nat) (coefficients : List Nat) : List (List Nat) :=
  let width:=networkOrder base coefficients
  leaderRow base coefficients::(groupRows width 1 (base+1)++
    ordinaryGroupRows width (base+2) base coefficients.tail.length)

def starMatrix (base : Nat) (coefficients : List Nat) : List (List Nat) :=
  let width:=networkOrder base coefficients
  leaderRow base coefficients::List.replicate (width-1) (oneHotRow width 0)

/-- The final round closes the path prefix by forwarding every nonleader
straight to the leader. -/
def networkRounds (base : Nat) (coefficients : List Nat) : List (List (List Nat)) :=
  List.replicate (base-1) (pathMatrix base coefficients)++[starMatrix base coefficients]

def networkLeaders (base : Nat) (coefficients : List Nat) : List Bool :=
  true::List.replicate (networkOrder base coefficients-1) false

end Counting.HardnessNetworkMachine
