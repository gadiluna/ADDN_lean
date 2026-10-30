import Counting.StackCompareLengthEquality
import Counting.StackEncodingPair

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def dimensionRoles : Fin 6 ↪ Fin 21 := ⟨![0,18,1,3,4,5],by decide⟩
def dimensionGuard : Routine 19 := sequence (Compare.preservingLengthEquality 15 dimensionRoles)
  (ofProgram (combineFlagsProgram 19 1))

/-- Compare two explicit cardinality counters, preserving both of them and
all other data. The count read from a list header must be unary. -/
theorem dimensionGuard_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail) (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[])
    (unary : store 18=List.replicate (store 18).length true) :
    ∃time ≤ 6*((store 0).length+(store 18).length)+15,
      Executes dimensionGuard store time
        (Function.update store 1 ((accepted && decide ((store 0).length=(store 18).length))::tail)) := by
  have comparing := Compare.preservingLengthEquality_executes 15 dimensionRoles store e3 e4 e5 unary
  change Executes (Compare.preservingLengthEquality 15 dimensionRoles) store
    (Compare.preservingLengthEqualityCost (store 0) (store 18))
    (Function.update store 1 (decide ((store 0).length=(store 18).length)::store 1)) at comparing
  rw [status] at comparing
  let flagged := Function.update store 1 (decide ((store 0).length=(store 18).length)::accepted::tail)
  have combining := combineFlags_executes 19 1 flagged accepted
    (decide ((store 0).length=(store 18).length)) tail (by simp [flagged])
  simp only [flagged,Function.update_idem] at combining
  have bound := Compare.preservingLengthEqualityCost_le (store 0) (store 18)
  exact ⟨_,by omega,comparing.sequence combining⟩

end Counting.StackMachine.NetworkRecognition
