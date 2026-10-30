import Counting.StackScaleLength
import Counting.StackUnaryMultiply

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Source clause count, width, output count, and three empty scratch registers. -/
abbrev CountWorkspace (extra : Nat) := Fin 6 ↪ Fin (extra+6)
def clauseCount (extra : Nat) (w : CountWorkspace extra) : Routine (extra+4) :=
  sequence (scaleLength (extra+3) (w 1) (w 3) (w 5) 3)
    (sequence (pushBit (w 3) true) (sequence (pushBit (w 3) true)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 4) (w 5)))
        (sequence (repeatedCopy (extra+3) (w 3) (w 4) (w 2) (w 5)) (clear (w 3))))))

theorem clauseCount_executes (extra : Nat) (w : CountWorkspace extra) (m width : Nat)
    (store : Fin (extra+6) → List Bool) (count : store (w 0)=List.replicate m true)
    (widthEq : (store (w 1)).length=width)
    (e2 : store (w 2)=[]) (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (clauseCount extra w) store (15*width*m+19*m+18*width+22)
      (Function.update store (w 2) (List.replicate (m*(3*width+2)) true)) := by
  have ne (i j : Fin 6) (h : i≠j) : w i≠w j := fun same=>h (w.injective same)
  have scaling := scaleLength_executes (extra+3) (w 1) (w 3) (w 5)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) 3 store e5
  rw [widthEq,e3,List.append_nil] at scaling
  let s1 := Function.update store (w 3) (List.replicate (3*width) true)
  let s2 := Function.update store (w 3) (List.replicate (3*width+1) true)
  let s3 := Function.update store (w 3) (List.replicate (3*width+2) true)
  have push1 : Executes (pushBit (w 3) true) s1 1 s2 := by
    simpa only [s1,s2,Function.update_self,Function.update_idem,List.replicate_succ] using pushBit_executes (w 3) true s1
  have push2 : Executes (pushBit (w 3) true) s2 1 s3 := by
    simpa only [s2,s3,Function.update_self,Function.update_idem,List.replicate_succ] using pushBit_executes (w 3) true s2
  have copying := copy_executes (extra+3) (w 0) (w 4) (w 5) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) s3
    (by simp [s3,w.injective.eq_iff,e5])
  let s4 := Function.update s3 (w 4) (List.replicate m true)
  have copyAs : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 4) (w 5))) s3 (5*m+2) s4 := by
    simpa [s4,s3,w.injective.eq_iff,count,e4] using copying
  have multiplying := unary_multiply_executes (extra+3) (w 3) (w 4) (w 2) (w 5)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (3*width+2) m s4
    (by simp [s4,s3,w.injective.eq_iff]) (by simp [s4]) (by simp [s4,s3,w.injective.eq_iff,e5])
  have targetEmpty : s4 (w 2)=[] := by simp [s4,s3,w.injective.eq_iff,e2]
  rw [targetEmpty,List.append_nil] at multiplying
  let s5 := Function.update (Function.update s4 (w 4) []) (w 2) (List.replicate (m*(3*width+2)) true)
  have clearing := clear_executes (w 3) s5
  have length : (s5 (w 3)).length+1=3*width+3 := by simp [s5,s4,s3,w.injective.eq_iff]
  rw [length] at clearing
  have result : Function.update s5 (w 3) []=Function.update store (w 2) (List.replicate (m*(3*width+2)) true) := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [w.injective.eq_iff,e3]
    · by_cases b : r=w 4
      · subst r;simp [s5,w.injective.eq_iff,e4]
      · simp [s5,s4,s3,Function.update_apply,a,b]
  rw [result] at clearing
  have combined := scaling.sequence (push1.sequence (push2.sequence (copyAs.sequence (multiplying.sequence clearing))))
  convert combined using 1
  · rfl
  · ring

end Counting.External.CNFMachine
