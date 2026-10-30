import Counting.ExternalFinalLiteralLoop
import Counting.StackEmitScaledNatural

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def finalHeaderSelection : Fin 6 ↪ Fin 12 := ⟨![1,3,7,5,6,11], by decide⟩
def CoordinateWorkspace.finalHeaderRoles (w : CoordinateWorkspace extra) : PolynomialWorkspace (extra+6) := finalHeaderSelection.trans w

/-- The full encoded final acceptance clause, including its runtime
literal-count header. The original time and width counters are preserved. -/
def finalClauseRoutine (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  sequence (finalLiterals extra w program)
    (emitScaledNatural (extra+6) w.finalHeaderRoles (finalOffsets program).length)

def finalClauseBound (program : Machine.Program) (time width : Nat) :=
  finalLiteralsBound program time width+1+emitScaledNaturalCoefficient (finalOffsets program).length*(width+1)^2

theorem finalClauseRoutine_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    (time width : Nat) (store : Fin (extra+12) → List Bool)
    (timeValue : store (w 0)=List.replicate time true)
    (widthValue : store (w 1)=List.replicate width true) (placeEmpty : store (w 2)=[])
    (empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ finalClauseBound program time width,
      Executes (finalClauseRoutine extra w program) store transitions
        (Function.update store (w 7)
          (clauseCodec.encode ((@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw)++store (w 7))) := by
  let literals := (@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw
  let middle := Function.update store (w 7) (Encoding.sequence literalCodec literals++store (w 7))
  obtain ⟨literalTime,literalBound,literalRun⟩ := finalLiterals_executes extra w program time width store timeValue widthValue placeEmpty empty
  obtain ⟨headerTime,headerBound,headerRun⟩ := emitScaledNatural_executes (extra+6) w.finalHeaderRoles (finalOffsets program).length middle
    (by simp [CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,w.injective.eq_iff,empty 3 (by simp)])
    (by simp [CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,w.injective.eq_iff,empty 5 (by simp)])
    (by simp [CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,w.injective.eq_iff,empty 6 (by simp)])
    (by simp [CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,w.injective.eq_iff,empty 11 (by simp)])
  have combined := literalRun.sequence headerRun
  refine ⟨literalTime+1+headerTime,?_,?_⟩
  · simp [CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,w.injective.eq_iff,widthValue] at headerBound
    unfold finalClauseBound
    omega
  · have length : literals.length=(finalOffsets program).length*width := by
      simp only [literals,List.length_map,finalClause_length]
    simpa +instances [finalClauseRoutine,CoordinateWorkspace.finalHeaderRoles,finalHeaderSelection,middle,
      w.injective.eq_iff,widthValue,clauseCodec,Encoding.list,length,List.append_assoc,literals] using combined

theorem finalClauseBound_polynomial (program : Machine.Program) (time width : Nat) :
    finalClauseBound program time width≤
      (centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)+
        emitScaledNaturalCoefficient (finalOffsets program).length+20)*((time+1)*(width+1)+1)^3 := by
  let size := (time+1)*(width+1)
  let coefficient := centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)
  let header := emitScaledNaturalCoefficient (finalOffsets program).length
  have hw : width≤size := by dsimp only [size]; nlinarith
  have hn : (time+1)*width≤size := by dsimp only [size]; nlinarith
  have power := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
  have weighted := Nat.mul_le_mul_left coefficient (Nat.mul_le_mul hw power)
  have cube : size*(size+1)^2≤(size+1)^3 := by nlinarith
  have finalWeighted := Nat.mul_le_mul_left coefficient cube
  have headerPower : (width+1)^2≤(size+1)^3 := by
    have power := Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2
    nlinarith
  have headerWeighted := Nat.mul_le_mul_left header headerPower
  have remainder : 7*size+5≤20*(size+1)^3 := by nlinarith
  change 5*width+4+width*(coefficient*((time+1)*width+1)^2+2)+1+header*(width+1)^2≤
    (coefficient+header+20)*(size+1)^3
  nlinarith

end Counting.External.CookLevin.StackGenerator
