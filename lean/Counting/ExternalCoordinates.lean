import Counting.ExternalCoordinateNext

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Source row, width, position; center, left, right, next; output; three
scratch cells and copy work. The output is untouched by coordinate computation. -/
abbrev CoordinateWorkspace (extra : Nat) := Fin 12 ↪ Fin (extra+12)

def centerSelection : Fin 6 ↪ Fin 12 := ⟨![0,1,2,3,8,11], by decide⟩
def leftSelection : Fin 6 ↪ Fin 12 := ⟨![3,1,2,4,8,11], by decide⟩
def rightSelection : Fin 7 ↪ Fin 12 := ⟨![3,1,2,5,8,9,11], by decide⟩
def nextSelection : Fin 6 ↪ Fin 12 := ⟨![3,1,2,6,8,11], by decide⟩

def CoordinateWorkspace.centerRoles (w : CoordinateWorkspace extra) : PolynomialWorkspace (extra+6) := centerSelection.trans w
def CoordinateWorkspace.leftRoles (w : CoordinateWorkspace extra) : PolynomialWorkspace (extra+6) := leftSelection.trans w
def CoordinateWorkspace.rightRoles (w : CoordinateWorkspace extra) : RightWorkspace (extra+5) := rightSelection.trans w
def CoordinateWorkspace.nextRoles (w : CoordinateWorkspace extra) : PolynomialWorkspace (extra+6) := nextSelection.trans w

def coordinates (extra : Nat) (w : CoordinateWorkspace extra) : Routine (extra+10) :=
  sequence (centerRoutine (extra+6) w.centerRoles)
    (sequence (leftRoutine (extra+6) w.leftRoles)
      (sequence (rightRoutine (extra+5) w.rightRoles) (nextRoutine (extra+6) w.nextRoles)))

def coordinateResult (w : CoordinateWorkspace extra) (store : Fin (extra+12) → List Bool) (round width place : Nat) :=
  let center := round*width+place
  Function.update (Function.update (Function.update (Function.update store
    (w 3) (List.replicate center true)) (w 4) (List.replicate (leftIndex center width place) true))
    (w 5) (List.replicate (rightIndex center width place) true)) (w 6) (List.replicate (center+width) true)

def coordinatesCost (round width place : Nat) :=
  let center := round*width+place
  centerCost round width place+leftCost center width place+
    rightPrepareCost center width place+rightFinishCost width place+(5*center+5*width+5)+4

theorem coordinates_executes (extra : Nat) (w : CoordinateWorkspace extra) (round width place : Nat)
    (store : Fin (extra+12) → List Bool)
    (roundValue : store (w 0)=List.replicate round true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    Executes (coordinates extra w) store (coordinatesCost round width place)
      (coordinateResult w store round width place) := by
  let center := round*width+place
  let s₁ := Function.update store (w 3) (List.replicate center true)
  let s₂ := Function.update s₁ (w 4) (List.replicate (leftIndex center width place) true)
  let s₃ := Function.update s₂ (w 5) (List.replicate (rightIndex center width place) true)
  have first : Executes (centerRoutine (extra+6) w.centerRoles) store (centerCost round width place) s₁ := by
    simpa +instances [CoordinateWorkspace.centerRoles,centerSelection,s₁,center] using
      centerRoutine_executes (extra+6) w.centerRoles round width place store
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using roundValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using widthValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using placeValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 3 (by simp))
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 8 (by simp))
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 11 (by simp))
  have second : Executes (leftRoutine (extra+6) w.leftRoles) s₁ (leftCost center width place) s₂ := by
    have run := leftRoutine_executes (extra+6) w.leftRoles center width place s₁
      (by simp [s₁,CoordinateWorkspace.leftRoles,leftSelection])
      (by simp [s₁,CoordinateWorkspace.leftRoles,leftSelection,w.injective.eq_iff,widthValue])
      (by simp [s₁,CoordinateWorkspace.leftRoles,leftSelection,w.injective.eq_iff,placeValue])
      (by simpa [s₁,CoordinateWorkspace.leftRoles,leftSelection,w.injective.eq_iff] using empty 4 (by simp))
      (by simpa [s₁,CoordinateWorkspace.leftRoles,leftSelection,w.injective.eq_iff] using empty 11 (by simp))
    simpa +instances [CoordinateWorkspace.leftRoles,leftSelection,s₂] using run
  have third : Executes (rightRoutine (extra+5) w.rightRoles) s₂
      (rightPrepareCost center width place+1+rightFinishCost width place) s₃ := by
    have run := rightRoutine_executes (extra+5) w.rightRoles center width place s₂
      (by simp [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff])
      (by simp [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff,widthValue])
      (by simp [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff,placeValue])
      (by simpa [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff] using empty 5 (by simp))
      (by simpa [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff] using empty 8 (by simp))
      (by simpa [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff] using empty 9 (by simp))
      (by simpa [s₂,s₁,CoordinateWorkspace.rightRoles,rightSelection,w.injective.eq_iff] using empty 11 (by simp))
    simpa +instances [CoordinateWorkspace.rightRoles,rightSelection,s₃] using run
  have fourth : Executes (nextRoutine (extra+6) w.nextRoles) s₃ (5*center+5*width+5)
      (coordinateResult w store round width place) := by
    have run := nextRoutine_executes (extra+6) w.nextRoles center width s₃
      (by simp [s₃,s₂,s₁,CoordinateWorkspace.nextRoles,nextSelection,w.injective.eq_iff])
      (by simp [s₃,s₂,s₁,CoordinateWorkspace.nextRoles,nextSelection,w.injective.eq_iff,widthValue])
      (by simpa [s₃,s₂,s₁,CoordinateWorkspace.nextRoles,nextSelection,w.injective.eq_iff] using empty 6 (by simp))
      (by simpa [s₃,s₂,s₁,CoordinateWorkspace.nextRoles,nextSelection,w.injective.eq_iff] using empty 11 (by simp))
    simpa +instances [CoordinateWorkspace.nextRoles,nextSelection,s₃,s₂,s₁,center,coordinateResult] using run
  have combined := first.sequence (second.sequence (third.sequence fourth))
  have cost : centerCost round width place+1+(leftCost center width place+1+
      (rightPrepareCost center width place+1+rightFinishCost width place+1+(5*center+5*width+5)))=
      coordinatesCost round width place := by unfold coordinatesCost; dsimp only [center]; omega
  simpa only [coordinates,cost] using combined

theorem coordinatesCost_bound (round width place bound : Nat) (hr : round≤bound) (hw : width≤bound) (hp : place≤bound) :
    coordinatesCost round width place ≤ 120*(bound+1)^2 := by
  have centerBound := centerCost_bound round width place bound hr hw hp
  have leftBound := leftCost_bound (round*width+place) width place
  have rightBound := rightCost_bound (round*width+place) width place
  have product := Nat.mul_le_mul hr hw
  unfold coordinatesCost
  dsimp only
  nlinarith

end Counting.External.CookLevin.StackGenerator
