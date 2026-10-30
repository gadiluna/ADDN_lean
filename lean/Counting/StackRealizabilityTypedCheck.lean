import Counting.StackRealizabilityDepthCounter
import Counting.StackRealizabilityInputBottom
import Counting.StackRealizabilityInputInitial

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def typedCheck : Routine 98 := sequence inputBottom
  (sequence inputInitial (sequence depthCounter roundScan))

def typedCheckCost (vista : Executable.Vista) (values : List Nat) (ell order : Nat) : Nat :=
  60*(((Encoding.list Encoding.natural).encode values).length+vista.nodes.size+1)+
  15000*((((Encoding.list Encoding.node).encode vista.nodes.toList).length+
    ((Encoding.list Encoding.natural).encode values).length)+ell.size+order.size+1)^5+
  100000*(((Encoding.list Encoding.node).encode vista.nodes.toList).length+vista.nodes.size+1)^4+
  3000000000000000000000000*(allRoundsSize vista values.toArray order)^25+3

def typedChecks (vista : Executable.Vista) (values : List Nat) (ell order : Nat) : Bool :=
  decide (RealizabilityVerifier.weight values.toArray vista.bottom=1) &&
    initialScanCheck vista.nodes.toList values ell order && checkedRounds vista values.toArray order

def typedResultStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  roundFile (roundInputData vista.nodes.toList values order (vista.node vista.bottom).level status
    (roundOuterData [] ![ell.bits,Encoding.vista.encode vista]))

/-- Every mathematical clause after syntax and array dimensions is now
implemented by a charged finite stack routine. The preceding total guards
must establish the two premises before this branch is entered. -/
theorem typedCheck_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (length : values.length=vista.nodes.size)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ typedCheckCost vista values ell order,
      Executes typedCheck (inputCountStore vista values ell order (accepted::tail)) time
        (typedResultStore vista values ell order ((accepted && typedChecks vista values ell order)::tail)) := by
  obtain ⟨t0,b0,r0⟩ := inputBottom_executes vista values ell order valid length accepted tail
  let afterBottom := accepted && decide (RealizabilityVerifier.weight values.toArray vista.bottom=1)
  obtain ⟨t1,b1,r1⟩ := inputInitial_executes vista values ell order length afterBottom tail
  let afterInitial := afterBottom && initialScanCheck vista.nodes.toList values ell order
  obtain ⟨t2,b2,r2⟩ := depthCounter_executes vista values ell order valid afterInitial tail
  obtain ⟨t3,b3,r3⟩ := roundScan_all vista values.toArray valid
    (by simpa only [List.size_toArray] using length) order afterInitial tail ![ell.bits,Encoding.vista.encode vista]
  have final : roundFile (roundInputData vista.nodes.toList values order (vista.node vista.bottom).level
      ((afterInitial && checkedRounds vista values.toArray order)::tail)
      (roundOuterData [] ![ell.bits,Encoding.vista.encode vista]))=
      typedResultStore vista values ell order ((accepted && typedChecks vista values ell order)::tail) := by
    simp only [typedResultStore,afterInitial,afterBottom,typedChecks,Bool.and_assoc]
  rw [final] at r3
  exact ⟨_,by unfold typedCheckCost;omega,r0.sequence (r1.sequence (r2.sequence r3))⟩

end Counting.StackMachine.RealizabilityCheck
