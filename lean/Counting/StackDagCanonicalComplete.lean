import Counting.StackDagCanonicalOneLevel
import Counting.StackDagCanonicalOuterLoop
import Counting.StackDagCanonicalOuterOutput

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

private theorem countedCost_bound (C L count time : Nat) (countBound : count ≤ L)
    (bound : time ≤ count*(C*(L+1)^135+2)+1) :
    time ≤ (C+3)*(L+1)^136 := by
  have scaled := Nat.mul_le_mul_right (C*(L+1)^135+2) (show count ≤ L+1 by omega)
  have linear : L+1 ≤ (L+1)^136 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ (L+1)^136 := Nat.one_le_pow' _ _
  have powers : (L+1)*(C*(L+1)^135)=C*(L+1)^136 := by
    rw [pow_succ (L+1) 135]
    exact (Nat.mul_left_comm (L+1) C ((L+1)^135)).trans
      (congrArg (C*·) (Nat.mul_comm (L+1) ((L+1)^135)))
  simp only [Nat.mul_add] at scaled bound
  rw [powers] at scaled
  rw [Nat.add_mul]
  omega

private theorem completeCost_bound (C A D N a b c : Nat) (positive : 1 ≤ N)
    (first : a ≤ A*N^4) (middle : b ≤ (C+3)*N^136) (last : c ≤ D*N^15) :
    a+1+(b+1+c) ≤ (C+A+D+10)*N^136 := by
  have p4 : N^4 ≤ N^136 := Nat.pow_le_pow_right positive (by decide)
  have p15 : N^15 ≤ N^136 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ N^136 := one_le_pow₀ positive
  have f := first.trans (Nat.mul_le_mul_left A p4)
  have l := last.trans (Nat.mul_le_mul_left D p15)
  rw [Nat.add_mul] at middle
  simp only [Nat.add_mul]
  omega

def canonicalLevelCoefficient : Nat := oneLevelCoefficient*101^27

theorem oneLevel_canonicalData_executes (source : Vista) (valid : NodesValid source)
    (level : Fin source.nodes.size) (counter : List Bool) (count : counter.length ≤ source.nodes.size) :
    ∃ time ≤ canonicalLevelCoefficient*((Encoding.vista.encode source).length+1)^135,
      Executes oneLevel (file (canonicalData source level.val counter)) time
        (file (canonicalData source (level.val+1) counter)) := by
  let state := canonicalPrefix source level.val
  let K := (Encoding.vista.encode source).length+1
  have cap := canonicalData_bounded source level.val counter (Nat.le_of_lt level.isLt) count
  have sameSize := (canonicalPrefix_encoded_polynomial source level.val (Nat.le_of_lt level.isLt)).2.2
  obtain ⟨time,bound,run⟩ := oneLevel_executes (canonicalData source level.val counter) source valid state level.val
    sameSize (by simp [canonicalData]) (by simp [canonicalData,state]) (by simp [canonicalData,state])
    (by simp [canonicalData]) (by simp [canonicalData]) (by simp [canonicalData])
    (by simp [canonicalData]) (by simp [canonicalData]) (100*K^5) cap
  have final : oneLevelData (canonicalData source level.val counter)
      (canonicalLevel source state level.val) level.val=canonicalData source (level.val+1) counter :=
    canonicalData_next source level.val counter
  rw [final] at run
  have positive : 1 ≤ K^5 := by dsimp [K];exact Nat.one_le_pow' _ _
  have base : 100*K^5+1 ≤ 101*K^5 := by omega
  have power := Nat.pow_le_pow_left base 27
  rw [Nat.mul_pow,←Nat.pow_mul] at power
  refine ⟨time,?_,run⟩
  calc
    time ≤ oneLevelCoefficient*(100*K^5+1)^27 := bound
    _ ≤ oneLevelCoefficient*(101^27*K^135) := Nat.mul_le_mul_left oneLevelCoefficient power
    _ = canonicalLevelCoefficient*K^135 := (Nat.mul_assoc oneLevelCoefficient (101^27) (K^135)).symm

def allCanonicalLevels : Routine 128 := forEach (context 24) oneLevel

theorem allCanonicalLevels_executes (source : Vista) (valid : NodesValid source) :
    ∃ time ≤ (canonicalLevelCoefficient+3)*((Encoding.vista.encode source).length+1)^136,
      Executes allCanonicalLevels (file (canonicalData source 0 (List.replicate source.nodes.size true))) time
        (file (canonicalData source source.nodes.size [])) := by
  obtain ⟨time,bound,run⟩ := canonicalLoop_executes source oneLevel
    (canonicalLevelCoefficient*((Encoding.vista.encode source).length+1)^135)
    (fun level counter count=>oneLevel_canonicalData_executes source valid level counter count)
    0 (List.replicate source.nodes.size true) (by simp)
  simp only [List.length_replicate,Nat.zero_add] at bound run
  exact ⟨time,countedCost_bound _ _ _ _ (canonical_source_count_bound source) bound,run⟩

def completeCanonical : Routine 128 := sequence initializeCanonical (sequence allCanonicalLevels output)

def completeCanonicalCoefficient : Nat :=
  canonicalLevelCoefficient+initializeCoefficient+canonicalOutputCoefficient+10

/-- Complete physical canonicalization of the shared DAG: collect remapped
signatures, stable-sort each level, commit and reindex, emit the new bottom,
and clear every work register. All costs refer to actual finite steps. -/
theorem completeCanonical_executes (source : Vista) (valid : NodesValid source)
    (nonempty : 0 < source.nodes.size) :
    ∃ time ≤ completeCanonicalCoefficient*((Encoding.vista.encode source).length+1)^136,
      Executes completeCanonical (inputStore 128 (Encoding.vista.encode source)) time
        (outputStore 128 (Encoding.vista.encode (canonicalize source))) := by
  obtain ⟨t0,b0,r0⟩ := initialize_canonicalData_executes source
  obtain ⟨t1,b1,r1⟩ := allCanonicalLevels_executes source valid
  obtain ⟨t2,b2,r2⟩ := output_canonicalData_executes source valid nonempty
  refine ⟨_,?_,r0.sequence (r1.sequence r2)⟩
  exact completeCost_bound canonicalLevelCoefficient initializeCoefficient canonicalOutputCoefficient
    _ _ _ _ (by omega) b0 b1 b2

end Counting.StackMachine.DagUpdate.Canonical
