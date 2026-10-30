import Counting.StackRealizabilityGraphFile

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def graphFieldsAnswer (tables : Fin 8→List Bool) (width : Nat) : Bool:=
  BitGraph.check width (arcTableValues tables width 0 0 width)
    (activeValues (tables 0) (tables 1) (tables 2) 0 width)

/-- Actual construction of both graph bit tables, bounded reachability, and
cleanup. All eight field tables and the unary width survive the checker. -/
def graphCheckRoutine : Routine 40:=sequence graphMatrixRoutine
  (sequence graphActiveRoutine (sequence graphReachRoutine (sequence (clear 10) (clear 13))))

theorem graphCheck_executes (tables : Fin 8→List Bool) (width : List Bool) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 30000000000*(graphSize tables width)^12,
      Executes graphCheckRoutine (graphFile tables width (accepted::tail) [] []) time
        (graphFile tables width ((accepted && graphFieldsAnswer tables width.length)::tail) [] []):=by
  let arcs:=arcTableValues tables width.length 0 0 width.length
  let active:=activeValues (tables 0) (tables 1) (tables 2) 0 width.length
  obtain ⟨matrixTime,matrixBound,matrixRun⟩:=graphMatrix_executes tables width (accepted::tail)
  obtain ⟨activeTime,activeBound,activeRun⟩:=graphActive_executes tables width (accepted::tail) arcs
  obtain ⟨checkTime,checkBound,checkRun⟩:=graphReach_executes tables width arcs active accepted tail
  let answer:=accepted && graphFieldsAnswer tables width.length
  let checked:=graphFile tables width (answer::tail) arcs active
  have clearArcs:=clear_executes (10:Fin 42) checked
  have arcsAt : checked 10=arcs:=by simp [checked,graphFile]
  rw [arcsAt] at clearArcs
  have clearArcsStore : Function.update checked 10 []=graphFile tables width (answer::tail) [] active:=by
    funext r
    by_cases same : r=10
    · subst r;simp [graphFile]
    · simp [checked,graphFile,same]
  rw [clearArcsStore] at clearArcs
  let halfway:=graphFile tables width (answer::tail) [] active
  have clearActive:=clear_executes (13:Fin 42) halfway
  have activeAt : halfway 13=active:=by simp [halfway,graphFile]
  rw [activeAt] at clearActive
  have final : Function.update halfway 13 []=graphFile tables width (answer::tail) [] []:=by
    funext r
    by_cases same : r=13
    · subst r;simp [graphFile]
    · simp [halfway,graphFile,same]
  rw [final] at clearActive
  have arcLength : arcs.length=width.length*width.length:=arcTableValues_length _ _ _ _ _
  have activeLength : active.length=width.length:=activeValues_length _ _ _ _ _
  rw [arcLength,activeLength] at checkBound
  rw [arcLength] at clearArcs
  rw [activeLength] at clearActive
  let S:=graphSize tables width
  have positive : 1≤S:=by dsimp only [S,graphSize];omega
  have widthBound : width.length≤S:=by dsimp only [S,graphSize];omega
  have squareWidth : width.length*width.length≤S^2:=by
    calc _≤S*S:=Nat.mul_le_mul widthBound widthBound
         _=S^2:=(pow_two S).symm
  have base : width.length*width.length+width.length+width.length+1≤4*S^2:=by
    have linear : S≤S^2:=Nat.le_self_pow (by decide) _
    have one : 1≤S^2:=Nat.one_le_pow _ _ positive
    omega
  have checkLimit : checkTime≤28672000000*S^12:=by
    have bound : checkTime≤7000000*(4*S^2)^6:=checkBound.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 6))
    have expansion (x : Nat) : 7000000*(4*x^2)^6=28672000000*x^12:=by ring
    exact expansion S ▸ bound
  have matrixLimit : matrixTime≤1000000*S^12:=matrixBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide)))
  have activeLimit : activeTime≤1000*S^12:=activeBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide)))
  have square : width.length*width.length≤S^12:=squareWidth.trans (Nat.pow_le_pow_right positive (by decide))
  have linear : width.length≤S^12:=widthBound.trans (Nat.le_self_pow (by decide) _)
  have one : 1≤S^12:=Nat.one_le_pow _ _ positive
  have execution:=matrixRun.sequence (activeRun.sequence (checkRun.sequence (clearArcs.sequence clearActive)))
  exact ⟨_,by change _≤30000000000*S^12;omega,execution⟩

theorem graphFieldsAnswer_fields (tables : Fin 8→List Bool) (width : Nat) :
    graphFieldsAnswer tables width=
      BitGraph.check width
        (CompactGraph.matrixBits (CompactGraph.fieldsArc (CompactGraph.fieldsFromBits width
          (tables 0) (tables 1) (tables 2) (tables 3) (tables 4) (tables 5) (tables 6) (tables 7))))
        (CompactGraph.vectorBits (CompactGraph.fieldsActive (CompactGraph.fieldsFromBits width
          (tables 0) (tables 1) (tables 2) (tables 3) (tables 4) (tables 5) (tables 6) (tables 7)))):=by
  unfold graphFieldsAnswer
  rw [arcTableValues_fields,activeValues_fields width (tables 0) (tables 1) (tables 2)
    (tables 3) (tables 4) (tables 5) (tables 6) (tables 7)]

end Counting.StackMachine.RealizabilityCheck
