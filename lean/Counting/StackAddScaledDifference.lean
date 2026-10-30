import Counting.StackSubtractLength
import Counting.StackPolynomialLength
import Counting.StackScaleLength

namespace Counting.StackMachine.Routine

/-- Roles: minuend, subtrahend, accumulator, difference, counter, copy work.
Append a scaled difference of lengths as unary bits, preserving both inputs. -/
def addScaledDifference (extra : Nat) (w : PolynomialWorkspace extra) (coefficient : Nat) : Routine (extra+4) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5)))
    (sequence (subtractLength (extra+2) (w 1) (w 3) (w 4) (w 5))
      (sequence (scaleLength (extra+3) (w 3) (w 2) (w 5) coefficient) (clear (w 3))))

def addScaledDifferenceCost (first second coefficient : Nat) :=
  5*first+7*second+10+coefficient*(5*(first-second)+3)+(first-second)

theorem addScaledDifference_executes (extra : Nat) (w : PolynomialWorkspace extra) (coefficient : Nat)
    (store : Fin (extra+6) → List Bool) (differenceEmpty : store (w 3)=[])
    (counterEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    Executes (addScaledDifference extra w coefficient) store
      (addScaledDifferenceCost (store (w 0)).length (store (w 1)).length coefficient)
      (Function.update store (w 2)
        (List.replicate (coefficient*((store (w 0)).length-(store (w 1)).length)) true++store (w 2))) := by
  let copied := Function.update store (w 3) (store (w 0))
  let shortened := Function.update store (w 3) ((store (w 0)).drop (store (w 1)).length)
  let payload := List.replicate (coefficient*((store (w 0)).length-(store (w 1)).length)) true++store (w 2)
  let added := Function.update shortened (w 2) payload
  have first : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5))) store
      (5*(store (w 0)).length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,copied,differenceEmpty,List.append_nil] using
      copy_executes (extra+3) (w 0) (w 3) (w 5)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store workEmpty
  have second : Executes (subtractLength (extra+2) (w 1) (w 3) (w 4) (w 5)) copied
      (7*(store (w 1)).length+4) shortened := by
    have run := subtractLength_executes (extra+2) (w 1) (w 3) (w 4) (w 5)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
      (by simp [w.injective.eq_iff]) copied
      (by simp [copied,w.injective.eq_iff,counterEmpty]) (by simp [copied,w.injective.eq_iff,workEmpty])
    simpa +instances [copied,shortened,w.injective.eq_iff] using run
  have third : Executes (scaleLength (extra+3) (w 3) (w 2) (w 5) coefficient) shortened
      (coefficient*(5*((store (w 0)).length-(store (w 1)).length)+3)) added := by
    have run := scaleLength_executes (extra+3) (w 3) (w 2) (w 5)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) coefficient shortened
      (by simp [shortened,w.injective.eq_iff,workEmpty])
    simpa [added,shortened,payload,w.injective.eq_iff] using run
  have fourth := clear_executes (w 3) added
  have restored : Function.update added (w 3) []=Function.update store (w 2) payload := by
    funext r
    by_cases a : r=w 3
    · subst r; simp [w.injective.eq_iff,differenceEmpty]
    · by_cases b : r=w 2 <;> simp [added,shortened,a,b]
  rw [restored] at fourth
  have combined := first.sequence (second.sequence (third.sequence fourth))
  have length : (added (w 3)).length=(store (w 0)).length-(store (w 1)).length := by
    simp [added,shortened,w.injective.eq_iff]
  rw [length] at combined
  simpa +instances only [addScaledDifference,ListPrograms.copyProgram,payload,addScaledDifferenceCost,show
    5*(store (w 0)).length+2+1+(7*(store (w 1)).length+4+1+
      (coefficient*(5*((store (w 0)).length-(store (w 1)).length)+3)+1+
        ((store (w 0)).length-(store (w 1)).length+1)))=
    5*(store (w 0)).length+7*(store (w 1)).length+10+
      coefficient*(5*((store (w 0)).length-(store (w 1)).length)+3)+((store (w 0)).length-(store (w 1)).length) by omega] using combined

theorem addScaledDifferenceCost_le (first second coefficient : Nat) :
    addScaledDifferenceCost first second coefficient≤(6+5*coefficient)*first+7*second+3*coefficient+10 := by
  have delta := Nat.sub_le first second
  have scaled := Nat.mul_le_mul_left coefficient (Nat.mul_le_mul_left 5 delta)
  unfold addScaledDifferenceCost
  nlinarith

end Counting.StackMachine.Routine
