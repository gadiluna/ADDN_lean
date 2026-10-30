import Counting.RealizabilityCompactFields
import Counting.EncodingNetworkSemantics

namespace Counting.StackMachine.NetworkRecognition
open RealizabilityVerifier

/-- The network validator activates every explicitly listed agent. This
removes the compact-certificate graph's inactive-slot convention. -/
theorem bitGraph_all_active (size : Nat) (arcs : List Bool) :
    BitGraph.check size arcs (List.replicate size true)=
      DirectedCounting.strongConnectivityCheck (BitGraph.edge size arcs) := by
  rw [BitGraph.check_eq]
  have active : (fun i:Fin size=>BitGraph.bitAt (List.replicate size true) i.val)=(fun _=>true) := by
    funext i
    simp [BitGraph.bitAt,i.isLt]
  rw [active]
  apply Bool.eq_iff_iff.mpr
  rw [DirectedCounting.strongConnectivityCheck_eq_true_iff]
  simp only [activeConnectedCheck,decide_eq_true_eq,forall_const,Fintype.card_fin]
  constructor
  · intro connected source target
    exact reachable_sound _ source size target (connected source target)
  · intro connected source target
    have all : reachable (BitGraph.edge size arcs) source size=Finset.univ := by
      simpa only [Fintype.card_fin] using reachable_complete _ connected source
    rw [all]
    exact Finset.mem_univ _

def matrixBits (size : Nat) (graph : Simulation.RoundGraph) : List Bool :=
  CompactGraph.matrixBits (fun source target:Fin size=>decide (0<Encoding.matrixEdge graph size source target))

@[simp] theorem matrixBits_length (size : Nat) (graph : Simulation.RoundGraph) :
    (matrixBits size graph).length=size*size := CompactGraph.matrixBits_length _

theorem matrixBits_edge (size : Nat) (graph : Simulation.RoundGraph) :
    BitGraph.edge size (matrixBits size graph)=
      (fun source target:Fin size=>decide (0<Encoding.matrixEdge graph size source target)) := by
  funext source target
  exact CompactGraph.bitAt_matrixBits _ source target

/-- No shape premise is needed for the semantic bridge: missing matrix
entries have the same zero default on both sides. Dimension validity is a
separate, explicitly checked condition. -/
theorem matrixBits_check (size : Nat) (graph : Simulation.RoundGraph) :
    BitGraph.check size (matrixBits size graph) (List.replicate size true)=
      DirectedCounting.strongConnectivityCheck
        (fun source target:Fin size=>decide (0<Encoding.matrixEdge graph size source target)) := by
  rw [bitGraph_all_active,matrixBits_edge]

end Counting.StackMachine.NetworkRecognition
