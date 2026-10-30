import Counting.StackGaussianRegisters
import Counting.StackGaussianSearch
import Counting.EncodingGaussianOperation
import Counting.StoredGaussianMatrixOperations

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- Mathematical relation for the live fields of a serialized solver state.
Indices and counters are actual stack words. The transcript is a sequence
of framed operations accompanied by its explicit unary count. -/
def stateSaved {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter flag : List Bool) : Fin 10 → List Bool :=
  ![List.replicate (pivot+1) true,List.replicate q true,candidate,[state.ok],
    Encoding.gaussianOpsRev (state.opsRev.map RawRowOp.ofRowOp),List.replicate state.opsRev.length true,
    row,counter,flag,[]]

def stateStore {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter flag : List Bool) : Fin 52 → List Bool :=
  ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)) [] [] []
    (stateSaved state pivot candidate row counter flag)

@[simp] theorem stateSaved_pivot {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter flag : List Bool) :
    stateSaved state pivot candidate row counter flag 0=List.replicate (pivot+1) true := rfl

@[simp] theorem stateSaved_dimension {q : Nat} (state : GaussianState q) (pivot : Nat)
    (candidate row counter flag : List Bool) :
    stateSaved state pivot candidate row counter flag 1=List.replicate q true := rfl

theorem searchSaved_stateSaved {q : Nat} (state : GaussianState q) (pivot : Nat)
    (oldCandidate row oldCounter oldFlag candidate counter flag : List Bool) :
    searchSaved (stateSaved state pivot oldCandidate row oldCounter oldFlag) candidate counter flag=
      stateSaved state pivot candidate row counter flag := by
  funext r;fin_cases r <;> simp [searchSaved,stateSaved]

theorem swapped_pivot_value {q : Nat} (state : GaussianState q) (pivot row : Fin q) :
    (StoredGaussian.emit state (.swap pivot row)).system.coeff pivot pivot=state.system.coeff row pivot := by
  simp [StoredGaussian.emit,applyRowOp,RowOp.transform]

/-- On actual successful search results the redundant zero test in the
mathematical implementation cannot fail. This needs no rank assumption. -/
theorem pivotStep_of_found {q : Nat} (state : GaussianState q) (pivot row : Fin q)
    (active : state.ok=true) (found : findPivot? state.system pivot=some row) :
    StoredGaussian.pivotStep state pivot=
      StoredGaussian.eliminateRows pivot (List.finRange q)
        (StoredGaussian.emit (StoredGaussian.emit state (.swap pivot row))
          (.scale pivot (state.system.coeff row pivot)⁻¹)) := by
  have nonzero := (DirectedCounting.GaussianGeneratorCompleteness.findPivot?_some_property state.system pivot row found).2
  simp only [StoredGaussian.pivotStep,active,if_true,found,swapped_pivot_value,if_neg nonzero]

end Counting.StackMachine.GaussianBank
