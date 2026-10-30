import Counting.ExternalCoordinateRight
import Counting.ExternalCellular

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Roles: center, width, unused, output, unused, copy work. -/
def nextRoutine (extra : Nat) (w : PolynomialWorkspace extra) : Routine (extra+4) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5)))
    (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5)))

theorem nextRoutine_executes (extra : Nat) (w : PolynomialWorkspace extra) (center width : Nat)
    (store : Fin (extra+6) → List Bool)
    (centerValue : store (w 0)=List.replicate center true)
    (widthValue : store (w 1)=List.replicate width true)
    (outputEmpty : store (w 3)=[]) (workEmpty : store (w 5)=[]) :
    Executes (nextRoutine extra w) store (5*center+5*width+5)
      (Function.update store (w 3) (List.replicate (center+width) true)) := by
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let copied := Function.update store (w 3) (List.replicate center true)
  have first : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5))) store
      (5*center+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,centerValue,outputEmpty,List.length_replicate,List.append_nil,copied] using
      copy_executes (extra+3) (w 0) (w 3) (w 5)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  have second : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) copied
      (5*width+2) (Function.update store (w 3) (List.replicate (center+width) true)) := by
    have run := copy_executes (extra+3) (w 1) (w 3) (w 5)
      (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) copied
      (by simp [copied,w.injective.eq_iff,workEmpty])
    have source : copied (w 1)=List.replicate width true := by simp [copied,w.injective.eq_iff,widthValue]
    have target : copied (w 3)=List.replicate center true := by simp [copied]
    simpa +instances only [ListPrograms.copyProgram,source,target,List.length_replicate,
      ← List.replicate_add,copied,Function.update_idem,Nat.add_comm width] using run
  have combined := first.sequence second
  simpa +instances only [ListPrograms.copyProgram,nextRoutine,
    show 5*center+2+1+(5*width+2)=5*center+5*width+5 by omega] using combined

theorem leftIndex_eq_ring (round : Nat) {width : Nat} (place : Fin width) :
    leftIndex (round*width+place.val) width place.val =
      round*width+((finRotate width).symm place).val := by
  obtain ⟨size,rfl⟩ := Nat.exists_eq_succ_of_ne_zero place.pos.ne'
  by_cases zero : place=0
  · subst place
    have rotated : (finRotate (size+1)).symm 0=Fin.last size :=
      (Equiv.symm_apply_eq _).2 finRotate_last.symm
    simp only [Fin.val_zero,leftIndex,ite_true,rotated,Fin.val_last]
    omega
  · have value : place.val ≠ 0 := fun h => zero (Fin.ext h)
    rw [leftIndex,if_neg value,coe_finRotate_symm_of_ne_zero zero]
    omega

theorem rightIndex_eq_ring (round : Nat) {width : Nat} (place : Fin width) :
    rightIndex (round*width+place.val) width place.val =
      round*width+(finRotate width place).val := by
  obtain ⟨size,rfl⟩ := Nat.exists_eq_succ_of_ne_zero place.pos.ne'
  rw [coe_finRotate]
  by_cases last : place=Fin.last size
  · subst place
    simp only [Fin.val_last,rightIndex,show size.succ-size-1=0 by omega,ite_true,Nat.add_zero]
    omega
  · have bound : place.val<size := Fin.val_lt_last last
    have nonzero : size+1-place.val-1 ≠ 0 := by omega
    simp only [rightIndex,nonzero,ite_false,last]
    omega

theorem nextIndex_eq (round width place : Nat) : (round*width+place)+width=(round+1)*width+place := by ring

end Counting.External.CookLevin.StackGenerator
