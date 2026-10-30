import Counting.StackGaussianOuter
import Counting.GaussianSerializedBounds

namespace Counting.StackMachine.GaussianBank
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem GaussianBits
set_option maxRecDepth 10000

def matrixBudget (q bits : Nat) : Nat := 40*(q+1)^2*(bits+1)
def factorBudget (bits : Nat) : Nat := 2*bits+3

def addBudget (q bits : Nat) : Nat :=
  (5*(q+1)+5*(q+1)+5)+1+
    (eliminationConstant*(6*(matrixBudget q bits+q+1))^16+1+
      (200*(q+q+factorBudget bits+10)^2+1+(factorBudget bits+1)))

def rowBudget (q bits : Nat) : Nat := 12*(q+1)+11+addBudget q bits+7

def swapBudget (q bits : Nat) : Nat :=
  (5*(q+1)+5*(q+1)+5)+1+(100*(matrixBudget q bits+1)+1+200*(q+q+15)^2)

def scaleBudget (q bits : Nat) : Nat :=
  (10*(q+1)+5)+1+(70000000000*(6*(matrixBudget q bits+q+1))^4+1+
    (200*(q+factorBudget bits+10)^2+1+(factorBudget bits+1)))

def allRowsBudget (q bits : Nat) : Nat := 5*q+4+1+(q*(rowBudget q bits+4)+1+1+(q+2))
def successBudget (q bits : Nat) : Nat :=
  2+1+(swapBudget q bits+1+(q+2+1+(scaleBudget q bits+1+allRowsBudget q bits)))
def pivotBudget (q bits : Nat) : Nat :=
  50000*(matrixBudget q bits+q+1)^2+1+(q+10+successBudget q bits+3)+3

theorem coefficient_length_bound {q : Nat} (system : RationalSystem q) (bits : Nat)
    (bounded : SystemBound bits system) (row column : Fin q) :
    (Encoding.rational.encode (system.coeff row column)).length ≤ factorBudget bits := by
  have coefficient := bounded row (some column)
  simp only [augmented,rationalBits] at coefficient
  rw [Encoding.rational_length]
  dsimp only [factorBudget]
  omega

theorem recordedAddCost_bound {q : Nat} (system : RationalSystem q) (target pivot : Fin q)
    (bits : Nat) (bounded : SystemBound bits system) : recordedAddCost system target pivot ≤ addBudget q bits := by
  have matrix := augmentedMatrix_encoded_bound system bits bounded
  have factor := coefficient_length_bound system bits bounded target pivot
  rw [←rational_neg_length (system.coeff target pivot)] at factor
  change _ ≤ matrixBudget q bits at matrix
  dsimp only [recordedAddCost,addBudget]
  gcongr <;> omega

theorem rowStepCost_bound {q : Nat} (system : RationalSystem q) (pivot row : Fin q)
    (bits : Nat) (bounded : SystemBound bits system) : rowStepCost system pivot row ≤ rowBudget q bits := by
  have comparison := Compare.preservingCost_le (List.replicate (pivot.val+1) true) (List.replicate (row.val+1) true)
  simp only [List.length_replicate] at comparison
  have arithmetic := recordedAddCost_bound system row pivot bits bounded
  dsimp only [rowStepCost,rowBudget]
  have pivotBound := pivot.isLt
  have rowBound := row.isLt
  omega

theorem recordedSwapCost_bound {q : Nat} (system : RationalSystem q) (pivot row : Fin q)
    (bits : Nat) (bounded : SystemBound bits system) : recordedSwapCost system pivot row ≤ swapBudget q bits := by
  have matrix := augmentedMatrix_encoded_bound system bits bounded
  change _ ≤ matrixBudget q bits at matrix
  dsimp only [recordedSwapCost,swapBudget]
  gcongr <;> omega

theorem recordedScaleCost_bound {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (bits : Nat) (bounded : SystemBound bits system) : recordedScaleCost system pivot ≤ scaleBudget q bits := by
  have matrix := augmentedMatrix_encoded_bound system bits bounded
  have factor := coefficient_length_bound system bits bounded pivot pivot
  rw [←rational_inv_length (system.coeff pivot pivot)] at factor
  change _ ≤ matrixBudget q bits at matrix
  dsimp only [recordedScaleCost,scaleBudget]
  gcongr <;> omega

/-- Uniform bounds are required only on the actual processed prefixes,
and are obtained from the minor invariant in the specialization below. -/
theorem rowsCost_bound {q : Nat} (pivot : Fin q) (start count : Nat) (state : GaussianState q)
    (bits : Nat) (inside : start+count ≤ q)
    (bounded : ∀ k ≤ count,SystemBound bits (StoredGaussian.eliminateCount pivot start k state).system) :
    rowsCost pivot start count state ≤ count*(rowBudget q bits+4)+1 := by
  induction count generalizing start state with
  | zero => simp [rowsCost]
  | succ count ih =>
    let row : Fin q := ⟨start,by omega⟩
    let next := StoredGaussian.eliminateAt pivot state start
    have head := rowStepCost_bound state.system pivot row bits (bounded 0 (by omega))
    have atHead : rowCostAt pivot state start=rowStepCost state.system pivot row := by simp [rowCostAt,row.isLt,row]
    have remaining : ∀ k ≤ count,SystemBound bits (StoredGaussian.eliminateCount pivot (start+1) k next).system := by
      intro k less
      exact bounded (k+1) (by omega)
    have tail := ih (start+1) next (by omega) remaining
    dsimp only [next] at tail
    simp only [rowsCost,atHead,Nat.add_mul,Nat.one_mul]
    omega

end Counting.StackMachine.GaussianBank
