import Counting.StackRealizabilityArcMatrix
import Counting.StackRealizabilityActiveVector
import Counting.RealizabilityCompactArcTable

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier.CompactGraph

theorem arcMatrix_fields_executes (store : Store 30) (empty : ArcWorkspaceEmpty store) :
    ∃ time ≤ 1000000*(arcReadSize store+(store 29).length)^7,
      Executes arcMatrix store time (Function.update store 30
        (matrixBits (fieldsArc (fieldsFromBits (store 29).length (store 0) (store 1) (store 2)
          (store 3) (store 4) (store 5) (store 6) (store 7))))):=by
  obtain ⟨time,bound,run⟩:=arcMatrix_executes store empty
  rw [arcTableValues_fields] at run
  exact ⟨time,bound,run⟩

theorem activeVector_fields_executes (store : Store 12)
    (e3 : store 3=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[]) (e8 : store 8=[])
    (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[]) :
    ∃ time ≤ 1000*((store 0).length+(store 1).length+(store 2).length+(store 4).length+1)^2,
      Executes activeVector store time (Function.update store 5
        (vectorBits (fieldsActive (fieldsFromBits (store 4).length (store 0) (store 1) (store 2)
          [] [] [] [] [])))):=by
  obtain ⟨time,bound,run⟩:=activeVector_executes store e3 e5 e6 e7 e8 e10 e11 e12 e13
  rw [activeValues_fields (store 4).length (store 0) (store 1) (store 2) [] [] [] [] []] at run
  exact ⟨time,bound,run⟩

end Counting.StackMachine.RealizabilityCheck
