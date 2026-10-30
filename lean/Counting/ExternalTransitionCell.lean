import Counting.ExternalCoordinateSemantics

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

/-- This program is fixed by the verifier machine. All dimensions and
indices are read from the three unary source registers. -/
def transitionCell (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  sequence (coordinates extra w)
    (sequence (scaleMany (extra+9) (w 8) (w 11) (Cellular.alphabet program) (coordinateTargets w))
      (sequence (transitionRoutine (extra+4) w.clauseRoles (Cellular.alphabet program)
        (Cellular.dynamics program (finRotate 0)).rule)
        (scaleMany (extra+9) (w 8) (w 11) 0 (coordinateTargets w))))

def transitionCoefficient (program : Machine.Program) :=
  multiClausesCoefficient (localTemplate (Cellular.alphabet program)
    (transitionAllowed (Cellular.dynamics program (finRotate 0)).rule))

def transitionCellBound (program : Machine.Program) (time width round place : Nat) :=
  let nodes := (time+1)*width
  let alphabet := Cellular.alphabet program
  coordinatesCost round width place+
    4*((7*alphabet+1)*nodes+3*alphabet+5)+
    transitionCoefficient program*(alphabet*nodes+1)^2+4*(alphabet*nodes+5)+3

theorem transitionCell_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    {time width : Nat} (round : Fin time) (place : Fin width) (store : Fin (extra+12) → List Bool)
    (roundValue : store (w 0)=List.replicate round.val true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place.val true)
    (empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ transitionCellBound program time width round.val place.val,
      Executes (transitionCell extra w program) store transitions
        (Function.update store (w 7)
          (Encoding.sequence clauseCodec
            ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
              (List.map CNFEncoding.literalRaw))++store (w 7))) := by
  let computed := coordinateResult w store round.val width place.val
  let scaled := scaledStore (coordinateTargets w) (Cellular.alphabet program) computed
  let payload := Encoding.sequence clauseCodec
    ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
      (List.map CNFEncoding.literalRaw))++store (w 7)
  let emitted := Function.update scaled (w 7) payload
  have outside (i : Fin 12) (h : i ∉ ([3,4,5,6] : List (Fin 12))) : w i ∉ coordinateTargets w := by
    simpa [coordinateTargets,w.injective.eq_iff] using h
  have computedEmpty (i : Fin 12) (h : i ∈ ([8,9,11] : List (Fin 12))) : computed (w i)=[] := by
    have notTarget : i ∉ ([3,4,5,6] : List (Fin 12)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl|rfl|rfl <;> decide
    rw [show computed (w i)=store (w i) from coordinateResult_outside w store _ _ _ _ (outside i notTarget)]
    apply empty i
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using Or.inr (Or.inr (Or.inr (Or.inr h)))
  have scaledEmpty (i : Fin 12) (h : i ∈ ([8,9,11] : List (Fin 12))) : scaled (w i)=[] := by
    have notTarget : i ∉ ([3,4,5,6] : List (Fin 12)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl|rfl|rfl <;> decide
    simpa only [scaled,scaledStore,if_neg (outside i notTarget)] using computedEmpty i h
  have coordinatesRun := coordinates_executes extra w round.val width place.val store roundValue widthValue placeValue empty
  have scaleRun := scaleMany_executes (extra+9) (w 8) (w 11) (Cellular.alphabet program) (coordinateTargets w)
    (coordinateTargets_unique w) (outside 8 (by decide)) (outside 11 (by decide))
    (by simp [w.injective.eq_iff]) computed (computedEmpty 8 (by simp)) (computedEmpty 11 (by simp))
  obtain ⟨emitTime,emitBound,emitter⟩ := transitionRoutine_executes (extra+4) w.clauseRoles
    (Cellular.dynamics program (finRotate width)) round place scaled
    (coordinateScaled_values w store program round place)
    (by simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using scaledEmpty 8 (by simp))
    (by simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using scaledEmpty 9 (by simp))
    (by simpa [CoordinateWorkspace.clauseRoles,coordinateClauseSelection] using scaledEmpty 11 (by simp))
  have outputPreserved : scaled (w 7)=store (w 7) := by
    rw [show scaled (w 7)=computed (w 7) by simp [scaled,scaledStore,coordinateTargets,w.injective.eq_iff]]
    exact coordinateResult_outside w store _ _ _ _ (outside 7 (by decide))
  have emitRun : Executes (transitionRoutine (extra+4) w.clauseRoles (Cellular.alphabet program)
      (Cellular.dynamics program (finRotate 0)).rule) scaled emitTime emitted := by
    simpa +instances [CoordinateWorkspace.clauseRoles,coordinateClauseSelection,outputPreserved,emitted,payload,Cellular.dynamics] using emitter
  have cleanRun := scaleMany_executes (extra+9) (w 8) (w 11) 0 (coordinateTargets w)
    (coordinateTargets_unique w) (outside 8 (by decide)) (outside 11 (by decide))
    (by simp [w.injective.eq_iff]) emitted
    (by simpa [emitted,w.injective.eq_iff] using scaledEmpty 8 (by simp))
    (by simpa [emitted,w.injective.eq_iff] using scaledEmpty 11 (by simp))
  have cleanResult : scaledStore (coordinateTargets w) 0 emitted=Function.update store (w 7) payload := by
    apply coordinate_cleanup w store round.val width place.val (Cellular.alphabet program) payload
    intro i hi
    apply empty i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    rcases hi with rfl|rfl|rfl|rfl <;> simp
  rw [cleanResult] at cleanRun
  have total := coordinatesRun.sequence (scaleRun.sequence (emitRun.sequence cleanRun))
  have scaleBound := scaleManyCost_bound (coordinateTargets w) (Cellular.alphabet program) computed ((time+1)*width)
    (coordinate_target_bound w store program round place)
  have emittedBound : ∀ target ∈ coordinateTargets w, (emitted target).length≤Cellular.alphabet program*((time+1)*width) := by
    intro target member
    have notOutput : target ≠ w 7 := by
      intro same
      simp [same,coordinateTargets,w.injective.eq_iff] at member
    simp only [emitted,Function.update_of_ne notOutput,scaled,scaledStore,if_pos member,List.length_replicate]
    exact Nat.mul_le_mul_left _ (coordinate_target_bound w store program round place target member)
  have cleanBound := scaleManyCost_bound (coordinateTargets w) 0 emitted (Cellular.alphabet program*((time+1)*width)) emittedBound
  refine ⟨coordinatesCost round.val width place.val+1+
    (scaleManyCost (coordinateTargets w) (Cellular.alphabet program) computed+1+
      (emitTime+1+scaleManyCost (coordinateTargets w) 0 emitted)),?_,?_⟩
  · simp only [show (coordinateTargets w).length=4 from rfl] at scaleBound cleanBound
    change emitTime≤transitionCoefficient program*(Cellular.alphabet program*((time+1)*width)+1)^2 at emitBound
    unfold transitionCellBound
    dsimp only
    omega
  · simpa only [transitionCell,computed,scaled,emitted,payload] using total

end Counting.External.CookLevin.StackGenerator
