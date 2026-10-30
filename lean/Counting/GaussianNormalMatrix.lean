import Counting.MachineMatrixSwapGaussian
import Counting.GaussianInputBounds

namespace Counting.GaussianNormalMatrix
open Counting.Executable
open DirectedCounting.VerifiedGaussianAnchorSolver

/-- A rectangular equation has exactly `width` coefficient entries and one
right-hand-side entry. Missing array entries use the solver's zero default. -/
def equationRow (width : Nat) (row : Equation) : List Rat :=
  List.ofFn (fun i : Fin width => row.1[i.val]?.getD 0) ++ [row.2]

def equationMatrix (width : Nat) (rows : List Equation) : List (List Rat) :=
  rows.map (equationRow width)

def column (matrix : List (List Rat)) (j : Nat) : List Rat :=
  matrix.map (fun row => row[j]?.getD 0)

def dot (left right : List Rat) : Rat := (List.zipWith (·*·) left right).sum

@[simp] theorem equationRow_length (width : Nat) (row : Equation) :
    (equationRow width row).length = width+1 := by simp [equationRow]

@[simp] theorem equationMatrix_length (width : Nat) (rows : List Equation) :
    (equationMatrix width rows).length = rows.length := by simp [equationMatrix]

@[simp] theorem column_length (matrix : List (List Rat)) (j : Nat) :
    (column matrix j).length = matrix.length := by simp [column]

theorem equationRow_coeff (width : Nat) (row : Equation) (j : Fin width) :
    (equationRow width row)[j.val]? = some (row.1[j.val]?.getD 0) := by
  rw [equationRow,List.getElem?_append_left (by simp)]
  simp only [List.getElem?_ofFn,dif_pos j.isLt]

theorem equationRow_rhs (width : Nat) (row : Equation) :
    (equationRow width row)[width]? = some row.2 := by
  rw [equationRow,List.getElem?_append_right (by simp)]
  simp

theorem equationRow_of_size (width : Nat) (row : Equation) (sized : row.1.size=width) :
    equationRow width row = row.1.toList ++ [row.2] := by
  unfold equationRow
  congr 1
  apply List.ext_getElem (by simp [sized])
  intro index leftBound _rightBound
  have inside : index < row.1.size := by simpa only [List.length_ofFn,sized] using leftBound
  simp only [List.getElem_ofFn,Array.getElem_toList,Array.getElem?_eq_getElem inside,Option.getD_some]

theorem equationMatrix_of_sized (width : Nat) (rows : List Equation) (sized : RowsSized width rows) :
    equationMatrix width rows = rows.map (fun row => row.1.toList ++ [row.2]) := by
  apply List.map_congr_left
  intro row member
  exact equationRow_of_size width row (sized row member)

theorem column_coeff (width : Nat) (rows : List Equation) (j : Fin width) :
    column (equationMatrix width rows) j.val = rows.map (fun row => row.1[j.val]?.getD 0) := by
  simp only [column,equationMatrix,List.map_map,Function.comp_def,equationRow_coeff,Option.getD_some]

theorem column_rhs (width : Nat) (rows : List Equation) :
    column (equationMatrix width rows) width = rows.map Prod.snd := by
  simp only [column,equationMatrix,List.map_map,Function.comp_def,equationRow_rhs,Option.getD_some]

theorem equationMatrix_column_selected (width : Nat) (rows : List Equation) (j : Fin (width+1)) :
    List.Forall₂ (fun row value => row[j.val]? = some value)
      (equationMatrix width rows) (column (equationMatrix width rows) j.val) := by
  induction rows with
  | nil => exact List.Forall₂.nil
  | cons row rows ih =>
    apply List.Forall₂.cons _ ih
    by_cases coefficient : j.val < width
    · simp only [equationRow_coeff width row ⟨j.val,coefficient⟩,Option.getD_some]
    · have last : j.val=width := by omega
      simp only [last,equationRow_rhs,Option.getD_some]

theorem dot_map {α : Type} (rows : List α) (left right : α → Rat) :
    dot (rows.map left) (rows.map right) = (rows.map (fun row => left row*right row)).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change left row*right row + dot (rows.map left) (rows.map right) =
      left row*right row + (rows.map (fun row => left row*right row)).sum
    rw [ih]

theorem normal_coeff_dot (width : Nat) (rows : List Equation) (i j : Fin width) :
    (normalSystem width rows).coeff i j =
      dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) j.val) := by
  rw [column_coeff,column_coeff,dot_map]
  rfl

theorem normal_rhs_dot (width : Nat) (rows : List Equation) (i : Fin width) :
    (normalSystem width rows).rhs i =
      dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) width) := by
  rw [column_coeff,column_rhs,dot_map]
  rfl

theorem augmentedRow_coeff {width : Nat} (system : RationalSystem width) (i j : Fin width) :
    (StoredGaussian.augmentedRow system i)[j.val]? = some (system.coeff i j) := by
  rw [StoredGaussian.augmentedRow,List.getElem?_append_left (by simp)]
  simp only [List.getElem?_ofFn,dif_pos j.isLt]

theorem augmentedRow_rhs {width : Nat} (system : RationalSystem width) (i : Fin width) :
    (StoredGaussian.augmentedRow system i)[width]? = some (system.rhs i) := by
  rw [StoredGaussian.augmentedRow,List.getElem?_append_right (by simp)]
  simp

theorem normal_row_dot (width : Nat) (rows : List Equation) (i : Fin width) (j : Fin (width+1)) :
    (StoredGaussian.augmentedRow (normalSystem width rows) i)[j.val]? =
      some (dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) j.val)) := by
  by_cases coefficient : j.val < width
  · rw [augmentedRow_coeff _ i ⟨j.val,coefficient⟩,normal_coeff_dot]
  · have last : j.val=width := by omega
    rw [last,augmentedRow_rhs,normal_rhs_dot]

theorem normal_row_ofFn (width : Nat) (rows : List Equation) (i : Fin width) :
    StoredGaussian.augmentedRow (normalSystem width rows) i =
      List.ofFn (fun j : Fin (width+1) =>
        dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) j.val)) := by
  apply List.ext_getElem?
  intro j
  by_cases inside : j < width+1
  · rw [normal_row_dot width rows i ⟨j,inside⟩]
    simp only [List.getElem?_ofFn,dif_pos inside]
  · rw [List.getElem?_eq_none (by simp;omega),List.getElem?_eq_none (by simp;omega)]

theorem normalMatrix_ofFn (width : Nat) (rows : List Equation) :
    StoredGaussian.augmentedMatrix (normalSystem width rows) =
      List.ofFn (fun i : Fin width => List.ofFn (fun j : Fin (width+1) =>
        dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) j.val))) := by
  unfold StoredGaussian.augmentedMatrix
  apply congrArg List.ofFn
  funext i
  exact normal_row_ofFn width rows i

theorem normal_dot_integral (width : Nat) (rows : List Equation)
    (coeffIntegral : ∀ r i, (rowMatrix width rows r i).den=1)
    (rhsIntegral : ∀ r, (rowRhs rows r).den=1)
    (i : Fin width) (j : Fin (width+1)) :
    (dot (column (equationMatrix width rows) i.val) (column (equationMatrix width rows) j.val)).den=1 := by
  by_cases coefficient : j.val < width
  · rw [←normal_coeff_dot width rows i ⟨j.val,coefficient⟩,
      GaussianBits.normal_coeff_cast width rows coeffIntegral]
    exact Rat.den_intCast _
  · have last : j.val=width := by omega
    rw [last,←normal_rhs_dot width rows i,
      GaussianBits.normal_rhs_cast width rows coeffIntegral rhsIntegral]
    exact Rat.den_intCast _

/-- The same dot primitive evaluates each original equation after solving. -/
theorem original_equation_dot (width : Nat) (row : Equation) (solution : Fin width → Rat) :
    dot (List.ofFn (fun i : Fin width => row.1[i.val]?.getD 0)) (List.ofFn solution) =
      ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0)*solution i)).sum := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,dot_map]

theorem original_equation_dot_sized (width : Nat) (row : Equation) (sized : row.1.size=width)
    (solution : Fin width → Rat) :
    dot row.1.toList (List.ofFn solution) =
      ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0)*solution i)).sum := by
  have coefficients : List.ofFn (fun i : Fin width => row.1[i.val]?.getD 0) = row.1.toList := by
    have equality := equationRow_of_size width row sized
    exact List.append_cancel_right equality
  rw [←coefficients]
  exact original_equation_dot width row solution

end Counting.GaussianNormalMatrix
