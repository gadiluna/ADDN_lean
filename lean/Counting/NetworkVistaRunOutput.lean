import Counting.NetworkVistaRunState
import Counting.StackRoutineClean
import Counting.StackRoutineMove

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 200000

def finish : Routine 128 := isolate (move 127 (context 2) 1 0)

theorem finish_executes (data : Fin 30→List Bool) (capacity : Nat)
    (bounded : ∀ r,(data r).length ≤ capacity) :
    ∃ time ≤ 140*(capacity+2),
      Executes finish (file data) time (outputStore 128 (data 2)) := by
  have moving := move_executes 127 (context 2) (1:Fin 130) 0
    (by decide) (by decide) (by decide) (file data) (by simp [file])
  rw [file_context,show file data 1=[] by simp [file],List.append_nil] at moving
  let moved := Function.update (Function.update (file data) 1 (data 2)) (context 2) []
  have movedBound : ∀ r,(moved r).length ≤ capacity := by
    intro r
    by_cases target : r=context 2
    · subst r;simp [moved]
    by_cases output : r=1
    · subst r;simpa [moved,context] using bounded 2
    simp only [moved,Function.update_of_ne target,Function.update_of_ne output]
    unfold file
    split
    · exact bounded _
    · simp
  obtain ⟨time,bound,clearing⟩ := clearRegisters_executes (workRegisters 128) moved capacity movedBound
  have final : clearedStore (workRegisters 128) moved=outputStore 128 (data 2) := by
    funext r
    by_cases output : r=1
    · subst r;simp [clearedStore,workRegisters,moved,outputStore,context]
    · simp [clearedStore,workRegisters,outputStore,output]
  rw [final] at clearing
  have count : (workRegisters 128).length ≤ 130 := by
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have bound' := bound.trans (Nat.mul_le_mul_right (capacity+2) count)
  refine ⟨_,?_,moving.sequence clearing⟩
  have source := bounded 2
  nlinarith

theorem finish_state_executes (input : Simulation.Input) :
    ∃ time ≤ 141000*((Encoding.networkInput.encode input).length+1)^6,
      Executes finish (file (stateData input input.rounds.size [])) time
        (outputStore 128 ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input))) := by
  obtain ⟨time,bound,run⟩ := finish_executes (stateData input input.rounds.size []) (stateCapacity input)
    (stateData_bounded input input.rounds.size [] (by omega) (by simp))
  have final : stateData input input.rounds.size [] 2=
      (Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input) := rfl
  rw [final] at run
  refine ⟨time,?_,run⟩
  have positive : 1≤((Encoding.networkInput.encode input).length+1)^6 := Nat.one_le_pow' _ _
  dsimp only [stateCapacity] at bound
  nlinarith

end Counting.StackMachine.NetworkVista.Run
