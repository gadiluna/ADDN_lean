import Counting.StackRealizabilityIncidenceMatrix
import Counting.RealizabilityCompactIncidenceTable

namespace Counting.StackMachine.RealizabilityCheck
open Routine

/-- Actual field tables, without requiring DAG validity: even a malformed
parent or incoming reference equal to the outside index is read exactly. -/
theorem incidenceMatrix_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (round : Nat)
    (source width : List Bool) (accepted : Bool) (tail suffix : List Bool)
    (input : source=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (counted : width.length=vista.nodes.size) :
    ∃ time ≤ 40000*(source.length+width.length+2)^8,
      Executes incidenceMatrix
        (incidenceTableFile source [] [] [] [] (accepted::tail) width [] []) time
        (Function.update (Function.update
          (incidenceTableFile source [] [] [] [] (accepted::tail) (false::width) [] [])
          0 (RealizabilityVerifier.CompactGraph.matrixBits
            (RealizabilityVerifier.CompactGraph.actualFields N vista weights round).incomingPositive))
          1 (RealizabilityVerifier.CompactGraph.matrixBits
            (RealizabilityVerifier.CompactGraph.actualFields N vista weights round).parentMatches)) := by
  simpa only [incomingMatrixValues_actual N vista weights round,parentMatrixValues_actual N vista weights round]
    using incidenceMatrix_executes vista.nodes.toList source width accepted tail suffix input
      (by simpa only [Array.length_toList] using counted)

end Counting.StackMachine.RealizabilityCheck
