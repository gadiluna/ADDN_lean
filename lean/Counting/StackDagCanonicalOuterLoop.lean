import Counting.StackDagCanonicalOuterState
import Counting.StackRoutineBasic

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false

/-- The counted outer loop pops its remaining-level counter before
executing a complete level, leaving the immutable source fields intact. -/
theorem canonicalLoop_executes (source : Vista) (routine : Routine 128) (bound : Nat)
    (each : ∀ (level : Fin source.nodes.size) (counter : List Bool),
      counter.length ≤ source.nodes.size →
      ∃ time ≤ bound, Executes routine (file (canonicalData source level.val counter)) time
        (file (canonicalData source (level.val+1) counter)))
    (level : Nat) (counter : List Bool) (within : level+counter.length ≤ source.nodes.size) :
    ∃ time ≤ counter.length*(bound+2)+1,
      Executes (forEach (context 24) routine) (file (canonicalData source level counter)) time
        (file (canonicalData source (level+counter.length) [])) := by
  induction counter generalizing level with
  | nil =>
    obtain ⟨run,halt⟩ := repeat_empty (context 24) routine (file (canonicalData source level []))
      (by simp [canonicalData])
    exact ⟨1,by simp,⟨1,file (canonicalData source level [])⟩,run,halt,by simp⟩
  | cons bit rest ih =>
    have levelBound : level < source.nodes.size := by simp only [List.length_cons] at within;omega
    obtain ⟨t0,b0,finish0,run0,halt0,store0⟩ := each ⟨level,levelBound⟩ rest
      (by simp only [List.length_cons] at within;omega)
    obtain ⟨t1,b1,finish1,run1,halt1,store1⟩ := ih (level+1)
      (by simp only [List.length_cons] at within;omega)
    have contents : file (canonicalData source level (bit::rest)) (context 24)=bit::rest := by simp [canonicalData]
    have consumed : Function.update (file (canonicalData source level (bit::rest))) (context 24) rest=
        file (canonicalData source level rest) := by rw [file_update,canonicalData_counter_update]
    have first := repeat_iteration (context 24) routine (file (canonicalData source level (bit::rest)))
      bit rest contents t0 finish0 (by simpa only [consumed] using run0) halt0
    refine ⟨t0+2+t1,?_,finish1,?_,halt1,?_⟩
    · simp only [List.length_cons];nlinarith
    · rw [Machine.run_add,first,Option.bind_some,store0]
      exact run1
    · simpa only [List.length_cons,show level+1+rest.length=level+(rest.length+1) by omega] using store1

end Counting.StackMachine.DagUpdate.Canonical
