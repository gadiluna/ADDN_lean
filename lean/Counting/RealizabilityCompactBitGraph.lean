import Counting.RealizabilityBitGraph
import Counting.RealizabilityCompactGraph

namespace Counting.RealizabilityVerifier.CompactGraph

/-- A row-major bit matrix and an active-slot vector represent precisely the
certificate graph. No slot is allocated per physical agent or multiplicity. -/
theorem bitCheck_eq (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat)
    (arcs flags : List Bool)
    (arcsExact : ∀ x y : Slot vista,
      BitGraph.bitAt arcs (x.val*(vista.nodes.size+1)+y.val)=arc N vista weights r x y)
    (flagsExact : ∀ x : Slot vista,BitGraph.bitAt flags x.val=active N vista weights r x) :
    BitGraph.check (vista.nodes.size+1) arcs flags=connectedCheck (roundArc N vista weights r) := by
  rw [BitGraph.check_eq]
  have edges : BitGraph.edge (vista.nodes.size+1) arcs=arc N vista weights r := by
    funext x y
    exact arcsExact x y
  have vertices : (fun x : Slot vista=>BitGraph.bitAt flags x.val)=active N vista weights r := by
    funext x
    exact flagsExact x
  rw [edges,vertices]
  exact check_eq N vista weights r

end Counting.RealizabilityVerifier.CompactGraph
