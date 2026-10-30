import Counting.GaussianNormalMatrix

namespace Counting.GaussianEquationCheck
open GaussianNormalMatrix

def vector (solution : List Rat) : List Rat := solution++[-1]
def accepts (rows : List (List Rat)) (solution : List Rat) : Bool :=
  rows.all (fun row => decide (dot row solution=0))

theorem dot_append_last (left right : List Rat) (same : left.length=right.length) (a b : Rat) :
    dot (left++[a]) (right++[b])=dot left right+a*b := by
  simp only [dot,List.zipWith_append same,List.zipWith_cons_cons,List.zipWith_nil_left,
    List.sum_append,List.sum_cons,List.sum_nil,add_zero]

theorem augmented_dot (width : Nat) (row : Executable.Equation) (solution : Fin width → Rat) :
    dot (equationRow width row) (vector (List.ofFn solution))=
      ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0)*solution i)).sum-row.2 := by
  rw [equationRow,vector,dot_append_last _ _ (by simp),original_equation_dot]
  ring

theorem accepts_original (width : Nat) (rows : List Executable.Equation) (solution : Fin width → Rat) :
    accepts (equationMatrix width rows) (vector (List.ofFn solution))=
      rows.all (fun row =>
        ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0)*solution i)).sum == row.2) := by
  simp only [accepts,equationMatrix,List.all_map,Function.comp_def,augmented_dot,sub_eq_zero]
  rfl

@[simp] theorem vector_length (solution : List Rat) : (vector solution).length=solution.length+1 := by
  simp [vector]

end Counting.GaussianEquationCheck
