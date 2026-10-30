import Counting.GaussianEquationCheck
import Counting.GaussianIntermediateActual

namespace Counting.GaussianSolveLinear
open GaussianNormalMatrix GaussianEquationCheck Executable GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

def result (width : Nat) (rows : List Equation) : Option (List Rat) := do
  let solution ← StoredGaussian.solve? (normalSystem width rows)
  if accepts (equationMatrix width rows) (vector (List.ofFn solution)) then
    some (List.ofFn solution) else none

/-- The internal matrix interface assumes the same width condition that
the public solver checks. Under it, the returned list is exactly the
public executable array, including singular and inconsistent failures. -/
theorem result_eq_solveLinear (width : Nat) (rows : List Equation) (sized : RowsSized width rows) :
    result width rows=(solveLinear? width rows).map Array.toList := by
  have widths : rows.all (fun row=>row.1.size==width)=true := by
    apply List.all_eq_true.mpr
    intro row member
    simp [sized row member]
  unfold result solveLinear?
  rw [widths]
  simp only [Bool.not_true]
  cases found : StoredGaussian.solve? (normalSystem width rows) with
  | none => rfl
  | some solution =>
    simp only [bind,Option.bind_some,accepts_original]
    split <;> simp [List.ofFn_eq_map]

theorem normal_integral (width : Nat) (rows : List Equation)
    (coeffIntegral : ∀ r i,(rowMatrix width rows r i).den=1)
    (rhsIntegral : ∀ r,(rowRhs rows r).den=1) :
    ∀ row column,(augmented (normalSystem width rows) row column).den=1 := by
  intro row column
  cases column with
  | none => simp [augmented,GaussianBits.normal_rhs_cast width rows coeffIntegral rhsIntegral]
  | some column => simp [augmented,GaussianBits.normal_coeff_cast width rows coeffIntegral]

end Counting.GaussianSolveLinear
