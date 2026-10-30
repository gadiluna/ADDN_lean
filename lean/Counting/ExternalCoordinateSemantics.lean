import Counting.ExternalCoordinates
import Counting.ExternalTransitionEmission
import Counting.StackScaleMany

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def coordinateClauseSelection : Fin 8 ↪ Fin 12 := ⟨![4,3,5,6,7,8,9,11], by decide⟩
def CoordinateWorkspace.clauseRoles (w : CoordinateWorkspace extra) : ClauseWorkspace (extra+4) := coordinateClauseSelection.trans w

def coordinateTargets (w : CoordinateWorkspace extra) : List (Fin (extra+12)) := [w 3,w 4,w 5,w 6]

theorem coordinateTargets_unique (w : CoordinateWorkspace extra) : (coordinateTargets w).Nodup := by
  simp [coordinateTargets,w.injective.eq_iff]

def coordinateValues (round width place : Nat) : Fin 4 → Nat :=
  let center := round*width+place
  ![leftIndex center width place,center,rightIndex center width place,center+width]

theorem coordinateResult_values (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool)
    (round width place : Nat) (position : Fin 4) :
    coordinateResult w store round width place (w.clauseRoles (position.castAdd 4))=
      List.replicate (coordinateValues round width place position) true := by
  fin_cases position <;> simp [coordinateResult,coordinateValues,CoordinateWorkspace.clauseRoles,
    coordinateClauseSelection,w.injective.eq_iff]

theorem coordinateValues_eq_position (program : Machine.Program) {time width : Nat}
    (round : Fin time) (place : Fin width) (position : Fin 4) :
    coordinateValues round.val width place.val position=
      ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).position position).val := by
  fin_cases position
  · change leftIndex (round.val*width+place.val) width place.val=((finRotate width).symm place).val+width*round.val
    simpa only [Nat.mul_comm,Nat.add_comm] using leftIndex_eq_ring round.val place
  · change round.val*width+place.val=place.val+width*round.val
    ring
  · change rightIndex (round.val*width+place.val) width place.val=(finRotate width place).val+width*round.val
    simpa only [Nat.mul_comm,Nat.add_comm] using rightIndex_eq_ring round.val place
  · change (round.val*width+place.val)+width=place.val+width*(round.val+1)
    ring

theorem coordinate_base_mem (w : CoordinateWorkspace extra) (position : Fin 4) :
    w.clauseRoles (position.castAdd 4) ∈ coordinateTargets w := by
  fin_cases position <;> simp [CoordinateWorkspace.clauseRoles,coordinateClauseSelection,coordinateTargets]

theorem coordinateScaled_values (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool)
    (program : Machine.Program) {time width : Nat} (round : Fin time) (place : Fin width) (position : Fin 4) :
    (scaledStore (coordinateTargets w) (Cellular.alphabet program)
      (coordinateResult w store round.val width place.val) (w.clauseRoles (position.castAdd 4))).length=
      Cellular.alphabet program*((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).position position).val := by
  rw [scaledStore,if_pos (coordinate_base_mem w position),List.length_replicate,
    coordinateResult_values,List.length_replicate,coordinateValues_eq_position program round place position]

theorem coordinate_target_bound (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool)
    (program : Machine.Program) {time width : Nat} (round : Fin time) (place : Fin width) (target : Fin (extra+12))
    (member : target ∈ coordinateTargets w) :
    (coordinateResult w store round.val width place.val target).length ≤ (time+1)*width := by
  have allPositions : ∀ position : Fin 4,
      (coordinateResult w store round.val width place.val (w.clauseRoles (position.castAdd 4))).length≤(time+1)*width := by
    intro position
    rw [coordinateResult_values,List.length_replicate,coordinateValues_eq_position program round place position]
    exact Nat.le_of_lt ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).position position).isLt
  simp only [coordinateTargets,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using allPositions 1
  · simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using allPositions 0
  · simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using allPositions 2
  · simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using allPositions 3

theorem coordinateResult_outside (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool)
    (round width place : Nat) (register : Fin (extra+12)) (outside : register ∉ coordinateTargets w) :
    coordinateResult w store round width place register=store register := by
  simp only [coordinateTargets,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  simp [coordinateResult,outside.1,outside.2.1,outside.2.2.1,outside.2.2.2]

theorem coordinate_cleanup (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool)
    (round width place alphabet : Nat) (payload : List Bool)
    (empty : ∀ i ∈ ([3,4,5,6] : List (Fin 12)), store (w i)=[]) :
    scaledStore (coordinateTargets w) 0
      (Function.update (scaledStore (coordinateTargets w) alphabet (coordinateResult w store round width place))
        (w 7) payload)=Function.update store (w 7) payload := by
  funext r
  by_cases member : r ∈ coordinateTargets w
  · have outside : r ≠ w 7 := by
      intro same
      simp [same,coordinateTargets,w.injective.eq_iff] at member
    have original : store r=[] := by
      simp only [coordinateTargets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl
      all_goals apply empty; simp
    simp [scaledStore,member,outside,original]
  · by_cases output : r=w 7
    · subst r; simp [scaledStore,member]
    · simp [scaledStore,member,output,coordinateResult_outside w store round width place r member]

end Counting.External.CookLevin.StackGenerator
