import Counting.NetworkVistaCollectPreserving
import Counting.NetworkVistaBundleSpec

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms

def physicalSenderPairs (n:Nat) (graph:Simulation.RoundGraph) (views:Fin n→Executable.Vista) :
    List (Executable.Vista×Array Nat) :=
  (List.finRange n).map (fun sender=>(views sender,graph[sender.val]?.getD #[]))

theorem physicalSenderPairs_length (n:Nat) (graph:Simulation.RoundGraph) (views:Fin n→Executable.Vista) :
    (physicalSenderPairs n graph views).length=n:=by simp [physicalSenderPairs]

theorem physicalSenderPairs_views (n:Nat) (graph:Simulation.RoundGraph) (views:Fin n→Executable.Vista) :
    (physicalSenderPairs n graph views).map Prod.fst=(Array.ofFn views).toList:=by
  simp [physicalSenderPairs,List.map_map,Array.toList_ofFn,List.ofFn_eq_map]

theorem physicalSenderPairs_rows (n:Nat) (graph:Simulation.RoundGraph) (views:Fin n→Executable.Vista)
    (size:graph.size=n) :
    (physicalSenderPairs n graph views).map Prod.snd=graph.toList:=by
  subst n
  simp only [physicalSenderPairs,List.map_map,Function.comp_def]
  have equal:Array.ofFn (fun sender:Fin graph.size=>graph[sender.val]?.getD #[])=graph:=by
    simp
  simpa only [Array.toList_ofFn,List.ofFn_eq_map] using congrArg Array.toList equal

/-- The actual preserving collector returns the same compact binary
bundles as the already-verified network semantics. Matrix identities are
confined to this offline adapter, never supplied to the local updater. -/
theorem collectPreserving_actual (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (e21:store 21=[]) (e22:store 22=[]) (e24:store 24=[]) (e25:store 25=[]) (e26:store 26=[])
    (n:Nat) (graph:Simulation.RoundGraph) (views:Fin n→Executable.Vista) (receiver:Fin n)
    (shape:Encoding.matrixShape n graph=true)
    (viewInput:store 37=(Encoding.array Encoding.vista).encode (Array.ofFn views))
    (rowInput:store 38=(Encoding.array (Encoding.array Encoding.natural)).encode graph)
    (position:(store 23).length=receiver.val) :
    ∃time ≤ Complexity.polynomial 26000 5
        ((store 37).length+(store 38).length+(store 23).length+n),
      Executes collectPreserving store time
        (Function.update store 27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
          (Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver))) := by
  have dimensions:=shape
  simp only [Encoding.matrixShape,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true] at dimensions
  have inside (pair) (member:pair∈physicalSenderPairs n graph views):receiver.val<pair.2.size:=by
    obtain ⟨sender,_,rfl⟩:=List.mem_map.mp member
    have index:sender.val<graph.size:=by have:=sender.isLt;omega
    have rowSize:(graph[sender.val]?.getD #[]).size=n:=by
      simpa only [Array.getElem?_eq_getElem index,Option.getD_some] using dimensions.2 sender.val index
    simpa only [rowSize] using receiver.isLt
  have inputViews:store 37=(Encoding.list Encoding.vista).encode
      ((physicalSenderPairs n graph views).map Prod.fst):=by
    rw [physicalSenderPairs_views]
    exact viewInput
  have inputRows:store 38=(Encoding.list (Encoding.array Encoding.natural)).encode
      ((physicalSenderPairs n graph views).map Prod.snd):=by
    rw [physicalSenderPairs_rows n graph views dimensions.1]
    exact rowInput
  obtain ⟨time,bound,run⟩:=collectPreserving_executes store accepted tail status empty e21 e22 e24 e25 e26
    receiver.val (physicalSenderPairs n graph views) inside inputViews inputRows position
  rw [physicalSenderPairs_length] at bound
  change Executes collectPreserving store time (Function.update store 27
    ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
      (receivedPairs receiver.val ((List.finRange n).map
        (fun sender=>(views sender,graph[sender.val]?.getD #[])))))) at run
  rw [receivedPairs_allAgents] at run
  exact ⟨time,bound,run⟩

end Counting.StackMachine.NetworkVista
