import Counting.ExternalCoverVerifierPrepare
import Counting.StackCompareLengthEquality
import Counting.StackEncodingListHeader

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def lengthPositions : Fin 6 ↪ Fin 64 := ⟨![33,25,1,43,44,45],by decide⟩
def lengthRoles (w : VerifierWorkspace extra) : Fin 6 ↪ Fin (extra+64) := lengthPositions.trans w

def witnessLength (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (Compare.preservingLengthEquality (extra+58) (lengthRoles w))
    (ofProgram (combineFlagsProgram (extra+62) (w 1)))

theorem witnessLength_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail)
    (unary : store (w 25)=List.replicate (store (w 25)).length true)
    (empty : ∀ i∈([43,44,45]:List (Fin 64)),store (w i)=[]) :
    ∃ time ≤ 6*((store (w 33)).length+(store (w 25)).length)+15,
      Executes (witnessLength extra w) store time
        (Function.update store (w 1)
          ((accepted && decide ((store (w 33)).length=(store (w 25)).length))::tail)) := by
  have comparing := Compare.preservingLengthEquality_executes (extra+58) (lengthRoles w) store
    (by simp [lengthRoles,lengthPositions,empty]) (by simp [lengthRoles,lengthPositions,empty])
    (by simp [lengthRoles,lengthPositions,empty]) (by simpa [lengthRoles,lengthPositions] using unary)
  let bit := decide ((store (w 33)).length=(store (w 25)).length)
  let compared := Function.update store (w 1) (bit::accepted::tail)
  have compareAs : Executes (Compare.preservingLengthEquality (extra+58) (lengthRoles w)) store
      (Compare.preservingLengthEqualityCost (store (w 33)) (store (w 25))) compared := by
    simpa [lengthRoles,lengthPositions,compared,bit,status] using comparing
  have combining := combineFlags_executes (extra+62) (w 1) compared accepted bit tail (by simp [compared])
  simp only [compared,Function.update_idem] at combining
  refine ⟨Compare.preservingLengthEqualityCost (store (w 33)) (store (w 25))+1+3,?_,compareAs.sequence combining⟩
  have bounded := Compare.preservingLengthEqualityCost_le (store (w 33)) (store (w 25))
  omega

end Counting.External.CoverVerification
