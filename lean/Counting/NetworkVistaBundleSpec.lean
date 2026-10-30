import Counting.NetworkVistaBundleValues

namespace Counting.StackMachine.NetworkVista

/-- The compact offline sender scan agrees with the existing global
adapter in the original sender order, including zero and missing entries. -/
theorem receivedPairs_senderBundles (n : Nat) (graph : Simulation.RoundGraph)
    (views : Fin n → Executable.Vista) (receiver : Fin n) (senders : List (Fin n)) :
    receivedPairs receiver.val (senders.map (fun sender=>(views sender,graph[sender.val]?.getD #[])))=
      Executable.senderBundles senders (Encoding.matrixEdge graph n) views receiver := by
  induction senders with
  | nil=>rfl
  | cons sender senders ih=>
    simp only [List.map_cons,receivedPairs,Executable.senderBundles,List.filterMap_cons,
      Encoding.matrixEdge]
    split <;> simp_all [Executable.senderBundles,Encoding.matrixEdge]

theorem receivedPairs_allAgents (n : Nat) (graph : Simulation.RoundGraph)
    (views : Fin n → Executable.Vista) (receiver : Fin n) :
    receivedPairs receiver.val ((List.finRange n).map (fun sender=>(views sender,graph[sender.val]?.getD #[])))=
      Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver :=
  receivedPairs_senderBundles n graph views receiver _

end Counting.StackMachine.NetworkVista
