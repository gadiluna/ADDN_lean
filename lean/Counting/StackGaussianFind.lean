import Counting.StackGaussianSearchPrepare
import Counting.StackGaussianNormalizationArithmetic
import Counting.StackGaussianPivot

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

abbrev findPivot : Routine 50 := sequence prepareSearch (sequence searchLoop (clear 39))

/-- Complete pivot search inside the shared register bank, including all
counter preparation and cleanup. The surviving flag is true exactly when
the search exhausted the eligible rows. -/
theorem findPivot_executes {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (saved : Fin 10 → List Bool) (hp : saved 0=List.replicate (pivot.val+1) true)
    (hd : saved 1=List.replicate q true) :
    ∃ time result exhausted,
      time ≤ 50000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+1)^2 ∧
      Executes findPivot
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] [] []
          (searchSaved saved [] [] [])) time
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] [] []
          (searchSaved saved (List.replicate (result+1) true) [] [exhausted])) ∧
      (if exhausted then none else some result)=(findPivot? system pivot).map Fin.val := by
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)
  have prepared := prepareSearch_executes matrix pivot.val q saved hp hd
  obtain ⟨time,result,exhausted,bounded,ran,correct⟩ := searchLoop_augmented system pivot saved
  have cleaned := clearSecond_executes matrix [] [] (List.replicate (pivot.val+1) true)
    (searchSaved saved (List.replicate (result+1) true) [] [exhausted])
  refine ⟨_,result,exhausted,?_,prepared.sequence (ran.sequence cleaned),correct⟩
  simp only [List.length_replicate]
  let size := matrix.length+q+1
  have indexBound := pivot.isLt
  have positive : 1 ≤ size := by dsimp [size];omega
  have countBound : q-pivot.val ≤ size := by dsimp [size];omega
  have pivotBound : pivot.val ≤ size := by dsimp [size];omega
  have dimensionBound : q ≤ size := by dsimp [size];omega
  have inner : matrix.length+q+pivot.val+(q-pivot.val)+7 ≤ 7*size := by dsimp [size];omega
  change time ≤ (q-pivot.val)*(5000*(matrix.length+q+pivot.val+(q-pivot.val)+7)+2)+1 at bounded
  change 17*pivot.val+5*q+32+1+(time+1+(pivot.val+1+1)) ≤ 50000*size^2
  have stepBound := Nat.mul_le_mul countBound (show
    5000*(matrix.length+q+pivot.val+(q-pivot.val)+7)+2 ≤ 35000*size+2 by omega)
  nlinarith

theorem findPivot_bounded_executes {q : Nat} (system : RationalSystem q) (pivot : Fin q)
    (saved : Fin 10 → List Bool) (hp : saved 0=List.replicate (pivot.val+1) true)
    (hd : saved 1=List.replicate q true) :
    ∃ time result exhausted,
      time ≤ 50000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+1)^2 ∧
      result ≤ q ∧
      Executes findPivot
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] [] []
          (searchSaved saved [] [] [])) time
        (ready (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] [] []
          (searchSaved saved (List.replicate (result+1) true) [] [exhausted])) ∧
      (if exhausted then none else some result)=(findPivot? system pivot).map Fin.val := by
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)
  let found := GaussianPivot.search (GaussianPivot.columnValue system pivot) (q-pivot.val) pivot.val
  have prepared := prepareSearch_executes matrix pivot.val q saved hp hd
  obtain ⟨time,bounded,ran⟩ := searchLoop_executes (StoredGaussian.augmentedMatrix system) pivot.val
    (GaussianPivot.columnValue system pivot) (GaussianPivot.augmented_entries system pivot)
    (q-pivot.val) pivot.val (by simp) saved
  have cleaned := clearSecond_executes matrix [] [] (List.replicate (pivot.val+1) true)
    (searchSaved saved (List.replicate (found.1+1) true) [] [found.2])
  have indexBound : found.1 ≤ q := by
    have upper := GaussianPivot.search_index_le (GaussianPivot.columnValue system pivot) (q-pivot.val) pivot.val
    have valid := pivot.isLt
    dsimp [found];omega
  refine ⟨_,found.1,found.2,?_,indexBound,prepared.sequence (ran.sequence cleaned),
    GaussianPivot.searchResult_findPivot system pivot⟩
  simp only [List.length_replicate]
  let size := matrix.length+q+1
  have pivotValid := pivot.isLt
  have positive : 1 ≤ size := by dsimp [size];omega
  have countBound : q-pivot.val ≤ size := by dsimp [size];omega
  have pivotBound : pivot.val ≤ size := by dsimp [size];omega
  have dimensionBound : q ≤ size := by dsimp [size];omega
  have inner : matrix.length+q+pivot.val+(q-pivot.val)+7 ≤ 7*size := by dsimp [size];omega
  simp only [StoredGaussian.augmentedMatrix_length] at bounded
  change time ≤ (q-pivot.val)*(5000*(matrix.length+q+pivot.val+(q-pivot.val)+7)+2)+1 at bounded
  change 17*pivot.val+5*q+32+1+(time+1+(pivot.val+1+1)) ≤ 50000*size^2
  have stepBound := Nat.mul_le_mul countBound (show
    5000*(matrix.length+q+pivot.val+(q-pivot.val)+7)+2 ≤ 35000*size+2 by omega)
  nlinarith

end Counting.StackMachine.GaussianBank
