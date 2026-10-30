import Counting.StackRealizabilityGraphCheck

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier

def graphTablesOfFields {size : Nat} (fields : CompactGraph.Fields size) : Fin 8→List Bool:=![
  CompactGraph.vectorBits fields.isNew,CompactGraph.vectorBits fields.isOld,
  CompactGraph.vectorBits fields.isOutside,CompactGraph.vectorBits fields.degreePositive,
  CompactGraph.vectorBits fields.leavingPositive,CompactGraph.vectorBits fields.deficitPositive,
  CompactGraph.matrixBits fields.parentMatches,CompactGraph.matrixBits fields.incomingPositive]

theorem graphSize_tabulated {size : Nat} (fields : CompactGraph.Fields size) (width : List Bool) :
    graphSize (graphTablesOfFields fields) width=6*size+2*size*size+width.length+1:=by
  simp [graphSize,graphTablesOfFields]
  ring

theorem graphFieldsAnswer_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (round : Nat) :
    graphFieldsAnswer (graphTablesOfFields (CompactGraph.actualFields N vista weights round))
      (vista.nodes.size+1)=connectedCheck (roundArc N vista weights round):=by
  rw [graphFieldsAnswer_fields]
  have fieldsEq : CompactGraph.fieldsFromBits (vista.nodes.size+1)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 0)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 1)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 2)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 3)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 4)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 5)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 6)
      (graphTablesOfFields (CompactGraph.actualFields N vista weights round) 7)=
        CompactGraph.actualFields N vista weights round:=
    CompactGraph.fieldsFromBits_tabulated _
  rw [fieldsEq]
  exact CompactGraph.tabulated_check_eq N vista weights round

/-- The graph subroutine consumes correctly tabulated fields and computes the
actual compact-certificate connectivity clause. StackRealizabilityMachine
integrates field construction into the complete certificate verifier. -/
theorem graphCheck_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (round : Nat)
    (width : List Bool) (dimension : width.length=vista.nodes.size+1)
    (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 30000000000*(graphSize (graphTablesOfFields (CompactGraph.actualFields N vista weights round)) width)^12,
      Executes graphCheckRoutine
        (graphFile (graphTablesOfFields (CompactGraph.actualFields N vista weights round)) width (accepted::tail) [] []) time
        (graphFile (graphTablesOfFields (CompactGraph.actualFields N vista weights round)) width
          ((accepted && connectedCheck (roundArc N vista weights round))::tail) [] []):=by
  obtain ⟨time,bound,run⟩:=graphCheck_executes (graphTablesOfFields (CompactGraph.actualFields N vista weights round))
    width accepted tail
  rw [dimension,graphFieldsAnswer_actual] at run
  exact ⟨time,bound,run⟩

end Counting.StackMachine.RealizabilityCheck
