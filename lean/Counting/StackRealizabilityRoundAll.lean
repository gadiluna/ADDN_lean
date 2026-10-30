import Counting.StackRealizabilityRoundScan
import Counting.RealizabilityVerifierBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def allRoundsSize (vista : Executable.Vista) (weights : Array Nat) (N : Nat) : Nat :=
  massInputSize vista.nodes.toList weights.toList+N.size+vista.nodes.size+
    (vista.node vista.bottom).level+4

private theorem outerCost_bound (count size : Nat) (bounded : count ≤ size) (positive : 1 ≤ size) :
    count*(2000000000000000000000000*size^24+2)+1 ≤
      3000000000000000000000000*size^25 := by
  have grow := Nat.mul_le_mul_right (2000000000000000000000000*size^24+2) bounded
  have power : 1 ≤ size^24 := Nat.one_le_pow _ _ positive
  rw [show size^25=size^24*size by rw [pow_succ]]
  nlinarith

/-- Complete ascending round scan. The input depth is an explicitly
prepared unary counter; its later extraction from the canonical DAG is
a separately charged prefix, not an oracle hidden in this theorem. -/
theorem roundScan_all (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (N : Nat) (accepted : Bool) (tail : List Bool) (auxiliary : Fin 2→List Bool) :
    ∃ time ≤ 3000000000000000000000000*(allRoundsSize vista weights N)^25,
      Executes roundScan
        (roundFile (roundInputData vista.nodes.toList weights.toList N 0 (accepted::tail)
          (roundOuterData (List.replicate (vista.node vista.bottom).level true) auxiliary))) time
        (roundFile (roundInputData vista.nodes.toList weights.toList N (vista.node vista.bottom).level
          ((accepted && checkedRounds vista weights N)::tail) (roundOuterData [] auxiliary))) := by
  obtain ⟨time,bound,run⟩ := roundScan_executes vista weights valid length N tail auxiliary
    (List.replicate (vista.node vista.bottom).level true) 0 accepted
  simp only [List.length_replicate,Nat.zero_add,checkedRounds_range'] at run
  refine ⟨time,?_,run⟩
  simp only [List.length_replicate,Nat.add_zero] at bound
  apply bound.trans
  exact outerCost_bound _ _ (by omega) (by omega)

end Counting.StackMachine.RealizabilityCheck
