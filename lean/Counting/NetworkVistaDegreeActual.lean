import Counting.NetworkVistaDegree
import Counting.NetworkVistaDegreeSpec

namespace Counting.StackMachine.NetworkVista
open Routine

/-- Binary row summation computes the outdegree in the physical network;
only this offline adapter mentions the receiver's finite identity. -/
theorem rowTotal_matrix (store:Store 20) (n:Nat) (graph:Simulation.RoundGraph)
    (shape:Encoding.matrixShape n graph=true) (agent:Fin n)
    (source:store 21=(Encoding.array Encoding.natural).encode (graph[agent.val]?.getD #[]))
    (work:∀r:Fin 22,r≠21 → store r=[]) :
    ∃time ≤ 2100*((store 21).length+1)^3,
      Executes rowTotal store time
        (Function.update store 19 (∑ target:Fin n,Encoding.matrixEdge graph n agent target).bits) := by
  simpa only [Encoding.matrix_row_sum n graph shape agent] using
    rowTotal_executes store (graph[agent.val]?.getD #[]) source work

end Counting.StackMachine.NetworkVista
