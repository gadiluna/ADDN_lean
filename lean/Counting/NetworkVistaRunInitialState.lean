import Counting.NetworkVistaRunInitial
import Counting.NetworkVistaRunState
import Counting.DagRawArray

namespace Counting.StackMachine.NetworkVista.Run

theorem setupData_eq_stateData (input : Simulation.Input) :
    setupData input=stateData input 0 (List.replicate input.rounds.size true) := by
  funext r
  fin_cases r <;> simp [setupData,stateData,Encoding.rawInputVistaArrayRun_initial,matrixCodec]

theorem setup_state_executes (input : Simulation.Input) :
    ∃ time ≤ setupCoefficient*((Encoding.networkInput.encode input).length+1)^3,
      setup.Executes (Routine.inputStore 128 (Encoding.networkInput.encode input)) time
        (RealizabilityCall.file (stateData input 0 (List.replicate input.rounds.size true))) := by
  simpa only [setupData_eq_stateData] using setup_executes input

end Counting.StackMachine.NetworkVista.Run
