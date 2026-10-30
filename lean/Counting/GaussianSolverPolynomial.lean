import Counting.StackGaussianComplete

/-! An explicit polynomial majorant for the composed solver budget. The
small arithmetic expression below is proved definitionally equal to the
actual budget; its bound uses only nonnegative sums, products and powers. -/
namespace Counting.StackMachine.GaussianBank

private inductive BudgetExpression where
  | constant (value : Nat)
  | dimension
  | bits
  | add (left right : BudgetExpression)
  | mul (left right : BudgetExpression)
  | pow (base : BudgetExpression) (exponent : Nat)

private instance : OfNat BudgetExpression n := ⟨.constant n⟩
private instance : Add BudgetExpression := ⟨.add⟩
private instance : Mul BudgetExpression := ⟨.mul⟩
private instance : Pow BudgetExpression Nat := ⟨.pow⟩

private def BudgetExpression.eval (q B : Nat) : BudgetExpression → Nat
  | .constant c => c
  | .dimension => q
  | .bits => B
  | .add a b => a.eval q B+b.eval q B
  | .mul a b => a.eval q B*b.eval q B
  | .pow a n => (a.eval q B)^n

private def BudgetExpression.degree : BudgetExpression → Nat
  | .constant _ => 0
  | .dimension => 1
  | .bits => 2
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree+b.degree
  | .pow a n => a.degree*n

private theorem BudgetExpression.bound (expression : BudgetExpression) (q B D : Nat)
    (positive : 1 ≤ D) (dimension : q ≤ D) (bits : B ≤ 6*D^2) :
    expression.eval q B ≤ expression.eval 1 6*D^expression.degree := by
  induction expression with
  | constant c => simp only [eval,degree,pow_zero,Nat.mul_one,le_refl]
  | dimension => simpa only [eval,degree,pow_one,Nat.one_mul] using dimension
  | bits => exact bits
  | add a b ha hb =>
    have left : a.eval q B ≤ a.eval 1 6*D^(max a.degree b.degree) :=
      ha.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _)))
    have right : b.eval q B ≤ b.eval 1 6*D^(max a.degree b.degree) :=
      hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _)))
    change a.eval q B+b.eval q B ≤ (a.eval 1 6+b.eval 1 6)*D^(max a.degree b.degree)
    rw [Nat.add_mul]
    exact Nat.add_le_add left right
  | mul a b ha hb =>
    have product := Nat.mul_le_mul ha hb
    change a.eval q B*b.eval q B ≤ (a.eval 1 6*b.eval 1 6)*D^(a.degree+b.degree)
    rw [pow_add]
    nlinarith only [product]
  | pow a n ha =>
    have powered := Nat.pow_le_pow_left ha n
    change (a.eval q B)^n ≤ (a.eval 1 6)^n*D^(a.degree*n)
    simpa only [Nat.mul_pow,←pow_mul] using powered

private def budgetExpression : BudgetExpression :=
  let q : BudgetExpression := .dimension
  let labelBits : BudgetExpression := .bits
  let matrix := 40*(q+1)^2*(labelBits+1)
  let factor := 2*labelBits+3
  let add := (5*(q+1)+5*(q+1)+5)+1+
    (BudgetExpression.constant eliminationConstant*(6*(matrix+q+1))^16+1+
      (200*(q+q+factor+10)^2+1+(factor+1)))
  let row := 12*(q+1)+11+add+7
  let swap := (5*(q+1)+5*(q+1)+5)+1+(100*(matrix+1)+1+200*(q+q+15)^2)
  let scale := (10*(q+1)+5)+1+(70000000000*(6*(matrix+q+1))^4+1+
    (200*(q+factor+10)^2+1+(factor+1)))
  let rows := 5*q+4+1+(q*(row+4)+1+1+(q+2))
  let success := 2+1+(swap+1+(q+2+1+(scale+1+rows)))
  let pivot := 50000*(matrix+q+1)^2+1+(q+10+success+3)+3
  let generator := 2000*(matrix+1)^3+1+(5*q+3+(q*(pivot+4)+1))
  generator+1+(5*q+3+2000*(matrix+q+2)^2+5)

private theorem budgetExpression_eq (q B : Nat) : budgetExpression.eval q B=solverBudget q B := rfl
private theorem budgetExpression_degree : budgetExpression.degree ≤ 100 := by decide

def solverPolynomialCoefficient : Nat := solverBudget 1 6
def solverPhysicalCoefficient : Nat := 20*(56+solverPolynomialCoefficient)^2

theorem solverBudget_polynomial (q B L : Nat) (dimension : q ≤ L) (bits : B ≤ 6*(L+1)^2) :
    solverBudget q B ≤ solverPolynomialCoefficient*(L+1)^100 := by
  have bound := BudgetExpression.bound budgetExpression q B (L+1) (by omega) (by omega) bits
  rw [budgetExpression_eq,budgetExpression_eq] at bound
  exact bound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) budgetExpression_degree))

theorem solverPhysical_polynomial (q B L : Nat) (dimension : q ≤ L) (bits : B ≤ 6*(L+1)^2) :
    20*(L+55+solverBudget q B)^2 ≤ solverPhysicalCoefficient*(L+1)^200 := by
  have bounded := solverBudget_polynomial q B L dimension bits
  have linear : L+1 ≤ (L+1)^100 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ (L+1)^100 := Nat.one_le_pow _ _ (by omega)
  have inside : L+55+solverBudget q B ≤ (56+solverPolynomialCoefficient)*(L+1)^100 := by
    nlinarith only [bounded,linear,one]
  have square := Nat.pow_le_pow_left inside 2
  have result := Nat.mul_le_mul_left 20 square
  simpa only [Nat.mul_pow,←pow_mul,solverPhysicalCoefficient,Nat.mul_assoc] using result

end Counting.StackMachine.GaussianBank
