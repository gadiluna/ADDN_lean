import Counting.NetworkVistaRunState
import Counting.StackRoutineBasic

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false

theorem stateData_counter_update (input : Simulation.Input) (depth : Nat) (counter rest : List Bool) :
    Function.update (stateData input depth counter) 21 rest=stateData input depth rest := by
  funext r
  fin_cases r <;> simp [stateData]

/-- Every body call receives the remaining round counter after the loop's
pop. The old configuration is replaced only by the proved complete round. -/
theorem roundLoop_executes (input : Simulation.Input) (routine : Routine 128) (bound : Nat)
    (each : ∀ (depth : Fin input.rounds.size) (counter : List Bool),
      counter.length ≤ input.rounds.size →
      ∃ time ≤ bound, Executes routine (file (stateData input depth.val counter)) time
        (file (stateData input (depth.val+1) counter)))
    (depth : Nat) (counter : List Bool) (within : depth+counter.length ≤ input.rounds.size) :
    ∃ time ≤ counter.length*(bound+2)+1,
      Executes (forEach (context 21) routine) (file (stateData input depth counter)) time
        (file (stateData input (depth+counter.length) [])) := by
  induction counter generalizing depth with
  | nil =>
    obtain ⟨run,halt⟩ := repeat_empty (context 21) routine (file (stateData input depth []))
      (by simp [stateData])
    exact ⟨1,by simp,⟨1,file (stateData input depth [])⟩,run,halt,by simp⟩
  | cons bit rest ih =>
    have depthBound : depth < input.rounds.size := by simp only [List.length_cons] at within;omega
    obtain ⟨t0,b0,finish0,run0,halt0,store0⟩ := each ⟨depth,depthBound⟩ rest
      (by simp only [List.length_cons] at within;omega)
    obtain ⟨t1,b1,finish1,run1,halt1,store1⟩ := ih (depth+1)
      (by simp only [List.length_cons] at within;omega)
    have contents : file (stateData input depth (bit::rest)) (context 21)=bit::rest := by simp [stateData]
    have consumed : Function.update (file (stateData input depth (bit::rest))) (context 21) rest=
        file (stateData input depth rest) := by rw [file_update,stateData_counter_update]
    have first := repeat_iteration (context 21) routine (file (stateData input depth (bit::rest)))
      bit rest contents t0 finish0 (by simpa only [consumed] using run0) halt0
    refine ⟨t0+2+t1,?_,finish1,?_,halt1,?_⟩
    · simp only [List.length_cons];nlinarith
    · rw [Machine.run_add,first,Option.bind_some,store0]
      exact run1
    · simpa only [List.length_cons,show depth+1+rest.length=depth+(rest.length+1) by omega] using store1

end Counting.StackMachine.NetworkVista.Run
