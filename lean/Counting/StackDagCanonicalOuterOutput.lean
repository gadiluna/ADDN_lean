import Counting.StackDagCanonicalOuterState
import Counting.StackDagCanonicalOutput

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def canonicalOutputCoefficient : Nat := 2200*101^3

/-- Finish at the exact executable canonical DAG, including its reindexed
bottom, and clear all remaining source, mapping and loop registers. -/
theorem output_canonicalData_executes (source : Vista) (valid : NodesValid source)
    (nonempty : 0 < source.nodes.size) :
    ∃ time ≤ canonicalOutputCoefficient*((Encoding.vista.encode source).length+1)^15,
      Executes output (file (canonicalData source source.nodes.size [])) time
        (outputStore 128 (Encoding.vista.encode (canonicalize source))) := by
  let state := canonicalPrefix source source.nodes.size
  let K := (Encoding.vista.encode source).length+1
  obtain ⟨time,bound,run⟩ := output_executes (canonicalData source source.nodes.size []) state.1 state.2
    source.bottom (by simp [canonicalData,state]) (by simp [canonicalData,state])
    (by simp [canonicalData]) (100*K^5) (canonicalData_bounded source source.nodes.size [] le_rfl (by simp))
  have final : (⟨state.1,state.2[source.bottom]?.getD 0⟩:Vista)=canonicalize source := by
    rw [canonicalize_eq_fold]
    rw [←canonicalPrefix_final source valid nonempty]
  rw [final] at run
  have positive : 1 ≤ K^5 := by dsimp [K];exact Nat.one_le_pow' _ _
  have base : 100*K^5+1 ≤ 101*K^5 := by omega
  have cube := Nat.pow_le_pow_left base 3
  rw [Nat.mul_pow,←Nat.pow_mul] at cube
  refine ⟨time,?_,run⟩
  calc
    time ≤ 2200*(100*K^5+1)^3 := bound
    _ ≤ 2200*(101^3*K^15) := Nat.mul_le_mul_left 2200 cube
    _ = canonicalOutputCoefficient*K^15 := (Nat.mul_assoc 2200 (101^3) (K^15)).symm

end Counting.StackMachine.DagUpdate.Canonical
