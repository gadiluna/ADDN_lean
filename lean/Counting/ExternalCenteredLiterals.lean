import Counting.ExternalTransitionCellCost

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def centeredLiteralSelection : Fin 5 ↪ Fin 12 := ⟨![4,7,5,6,11], by decide⟩
def CoordinateWorkspace.centeredLiteralRoles (w : CoordinateWorkspace extra) : PowerWorkspace (extra+7) := centeredLiteralSelection.trans w

/-- Emit fixed offsets from the runtime base `alphabet*(round*width+place)`.
Only output changes; all coordinate and codec scratch registers are cleared. -/
def centeredLiterals (extra : Nat) (w : CoordinateWorkspace extra) (alphabet : Nat)
    (literals : List (Nat × Bool)) : Routine (extra+10) :=
  sequence (centerRoutine (extra+6) w.centerRoles)
    (sequence (scaleLength (extra+9) (w 3) (w 4) (w 11) alphabet)
      (sequence (emitOffsetList (extra+7) w.centeredLiteralRoles literals)
        (sequence (clear (w 3)) (clear (w 4)))))

def centeredLiteralsBound (alphabet : Nat) (literals : List (Nat × Bool)) (round width place : Nat) :=
  let center := round*width+place
  centerCost round width place+alphabet*(5*center+3)+
    offsetListCoefficient literals*(alphabet*center+1)^2+center+alphabet*center+6

theorem centeredLiterals_executes (extra : Nat) (w : CoordinateWorkspace extra) (alphabet : Nat)
    (literals : List (Nat × Bool)) (round width place : Nat) (store : Fin (extra+12) → List Bool)
    (roundValue : store (w 0)=List.replicate round true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (empty : ∀ i ∈ ([3,4,5,6,8,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ centeredLiteralsBound alphabet literals round width place,
      Executes (centeredLiterals extra w alphabet literals) store transitions
        (Function.update store (w 7)
          (Encoding.sequence literalCodec (shiftedLiterals (alphabet*(round*width+place)) literals)++store (w 7))) := by
  have distinct {a b : Fin 12} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let center := round*width+place
  let computed := Function.update store (w 3) (List.replicate center true)
  let scaled := Function.update computed (w 4) (List.replicate (alphabet*center) true)
  let payload := Encoding.sequence literalCodec (shiftedLiterals (alphabet*center) literals)++store (w 7)
  let emitted := Function.update scaled (w 7) payload
  have computeRun : Executes (centerRoutine (extra+6) w.centerRoles) store (centerCost round width place) computed := by
    simpa +instances [CoordinateWorkspace.centerRoles,centerSelection,computed,center] using
      centerRoutine_executes (extra+6) w.centerRoles round width place store
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using roundValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using widthValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using placeValue)
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 3 (by simp))
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 8 (by simp))
        (by simpa [CoordinateWorkspace.centerRoles,centerSelection] using empty 11 (by simp))
  have scaleRun : Executes (scaleLength (extra+9) (w 3) (w 4) (w 11) alphabet) computed (alphabet*(5*center+3)) scaled := by
    have run := scaleLength_executes (extra+9) (w 3) (w 4) (w 11)
      (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) alphabet computed
      (by simp [computed,w.injective.eq_iff,empty 11 (by simp)])
    simpa +instances [computed,scaled,w.injective.eq_iff,empty 4 (by simp)] using run
  obtain ⟨emitTime,emitBound,emitRun⟩ := emitOffsetList_executes (extra+7) w.centeredLiteralRoles literals scaled
    (by simp [CoordinateWorkspace.centeredLiteralRoles,centeredLiteralSelection,scaled,computed,w.injective.eq_iff,empty 5 (by simp)])
    (by simp [CoordinateWorkspace.centeredLiteralRoles,centeredLiteralSelection,scaled,computed,w.injective.eq_iff,empty 6 (by simp)])
    (by simp [CoordinateWorkspace.centeredLiteralRoles,centeredLiteralSelection,scaled,computed,w.injective.eq_iff,empty 11 (by simp)])
  have emission : Executes (emitOffsetList (extra+7) w.centeredLiteralRoles literals) scaled emitTime emitted := by
    simpa +instances [CoordinateWorkspace.centeredLiteralRoles,centeredLiteralSelection,emitted,payload,scaled,computed,w.injective.eq_iff] using emitRun
  let firstClear := Function.update emitted (w 3) []
  have clearCenter : Executes (clear (w 3)) emitted (center+1) firstClear := by
    simpa only [emitted,scaled,computed,Function.update_of_ne (distinct (by decide : (3:Fin 12)≠7)),
      Function.update_of_ne (distinct (by decide : (3:Fin 12)≠4)),Function.update_self,List.length_replicate,firstClear] using
      clear_executes (w 3) emitted
  have clearBase : Executes (clear (w 4)) firstClear (alphabet*center+1) (Function.update store (w 7) payload) := by
    have run := clear_executes (w 4) firstClear
    have value : firstClear (w 4)=List.replicate (alphabet*center) true := by simp [firstClear,emitted,scaled,w.injective.eq_iff]
    have result : Function.update firstClear (w 4) []=Function.update store (w 7) payload := by
      funext r
      by_cases a : r=w 4
      · subst r; simp [w.injective.eq_iff,empty 4 (by simp)]
      · by_cases b : r=w 3
        · subst r; simp [firstClear,w.injective.eq_iff,empty 3 (by simp)]
        · by_cases c : r=w 7
          · subst r; simp [firstClear,emitted,w.injective.eq_iff]
          · simp [firstClear,emitted,scaled,computed,a,b,c]
    simpa only [value,List.length_replicate,result] using run
  have combined := computeRun.sequence (scaleRun.sequence (emission.sequence (clearCenter.sequence clearBase)))
  refine ⟨centerCost round width place+1+(alphabet*(5*center+3)+1+(emitTime+1+(center+1+1+(alphabet*center+1)))),?_,?_⟩
  · simp [CoordinateWorkspace.centeredLiteralRoles,centeredLiteralSelection,scaled] at emitBound
    change _≤centerCost round width place+alphabet*(5*center+3)+offsetListCoefficient literals*(alphabet*center+1)^2+center+alphabet*center+6
    omega
  · simpa only [centeredLiterals,payload,center] using combined

end Counting.External.CookLevin.StackGenerator
