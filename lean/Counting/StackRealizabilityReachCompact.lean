import Counting.StackRealizabilityReachCheck
import Counting.RealizabilityCompactBitGraph

namespace Counting.StackMachine.RealizabilityCheck
open Routine

/-- The concrete bit-matrix checker implements compact-certificate connectivity.
StackRealizabilityGraphTables supplies the input tables and their construction cost. -/
theorem reachCheck_compact (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (round : Nat)
    (store : Store 22) (value : Bool) (tail : List Bool)
    (accumulated : store 19=value::tail) (empty : RowEmpty store) (e17 : store 17=[]) (e23 : store 23=[])
    (width : (store 2).length=vista.nodes.size+1)
    (arcsExact : ∀ x y : RealizabilityVerifier.CompactGraph.Slot vista,
      RealizabilityVerifier.BitGraph.bitAt (store 0) (x.val*(vista.nodes.size+1)+y.val)=
        RealizabilityVerifier.CompactGraph.arc N vista weights round x y)
    (flagsExact : ∀ x : RealizabilityVerifier.CompactGraph.Slot vista,
      RealizabilityVerifier.BitGraph.bitAt (store 18) x.val=
        RealizabilityVerifier.CompactGraph.active N vista weights round x) :
    ∃ time ≤ 7000000*((store 0).length+(store 18).length+(vista.nodes.size+1)+1)^6,
      Executes reachCheckRoutine store time (Function.update store 19
        ((value && RealizabilityVerifier.connectedCheck
          (RealizabilityVerifier.roundArc N vista weights round))::tail)):=by
  obtain ⟨time,bound,ran⟩:=reachCheck_executes store value tail accumulated empty e17 e23
  rw [width] at bound ran
  rw [RealizabilityVerifier.CompactGraph.bitCheck_eq N vista weights round (store 0) (store 18) arcsExact flagsExact] at ran
  exact ⟨time,bound,ran⟩

end Counting.StackMachine.RealizabilityCheck
