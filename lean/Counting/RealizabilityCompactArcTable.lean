import Counting.StackRealizabilityArcValues
import Mathlib.Data.List.OfFn

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier.CompactGraph
set_option backward.isDefEq.respectTransparency false

theorem arcRowValues_ofFn (tables : Fin 8→List Bool) (width x y xy yx count : Nat) :
    arcRowValues tables width x y xy yx count=
      List.ofFn (fun j : Fin count=>arcCell tables x (y+j.val) (xy+j.val) (yx+j.val*width)) := by
  induction count generalizing y xy yx with
  | zero=>rfl
  | succ count ih=>
    rw [arcRowValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Nat.zero_mul,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext j
    congr 1 <;> ring

theorem arcTableValues_ofFn (tables : Fin 8→List Bool) (width x xy count : Nat) :
    arcTableValues tables width x xy count=
      (List.ofFn (fun i : Fin count=>
        arcRowValues tables width (x+i.val) 0 (xy+i.val*width) (x+i.val) width)).flatten := by
  induction count generalizing x xy with
  | zero=>rfl
  | succ count ih=>
    rw [arcTableValues,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Nat.zero_mul,Fin.val_succ]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    congr 1 <;> ring

/-- The physical counters enumerate every sender/receiver pair in row-major
order. Incoming incidences deliberately use the transposed index. No table
well-formedness assumption is needed for this Boolean-field bridge. -/
theorem arcTableValues_fields (tables : Fin 8→List Bool) (width : Nat) :
    arcTableValues tables width 0 0 width=
      matrixBits (fieldsArc (fieldsFromBits width (tables 0) (tables 1) (tables 2)
        (tables 3) (tables 4) (tables 5) (tables 6) (tables 7))) := by
  rw [arcTableValues_ofFn,matrixBits,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext x
  rw [arcRowValues_ofFn]
  apply congrArg List.ofFn
  funext y
  have encoded : (⟨x.val*width+y.val,by have := x.isLt;have := y.isLt;nlinarith⟩ : Fin (width*width))=
      finProdFinEquiv (x,y) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [Nat.zero_add,encoded,Equiv.symm_apply_apply]
  simp only [arcCell,fieldsArc,fieldsFromBits,Nat.add_comm]

end Counting.StackMachine.RealizabilityCheck
