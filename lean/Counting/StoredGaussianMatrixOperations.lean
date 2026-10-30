import Counting.MachineMatrixSwapGaussian
import Counting.MachineRowAxpyGaussian

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- A selected-row scaling result is reinserted into the full stored matrix.
The equation covers the right-hand side and every untouched row. -/
theorem scale_augmentedMatrix {q : Nat} (system : RationalSystem q) (row : Fin q) (factor : Rat) :
    augmentedMatrix (materialize (system.applyRowOp (.scale row factor)))=
      (augmentedMatrix system).set row.val ((augmentedRow system row).map (factor*·)) := by
  apply List.ext_getElem (by simp)
  intro index _leftBound _rightBound
  by_cases selected : index=row.val
  · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,selected,
      List.map_ofFn,Function.comp_def]
  · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,selected,Ne.symm selected]

/-- Full matrix correspondence for the actual target-plus-scaled-source
operation, including the case of equal indices in its total extension. -/
theorem add_augmentedMatrix {q : Nat} (system : RationalSystem q) (target source : Fin q) (factor : Rat) :
    augmentedMatrix (materialize (system.applyRowOp (.add target source factor)))=
      (augmentedMatrix system).set target.val
        (List.zipWith (fun a b => a+factor*b) (augmentedRow system target) (augmentedRow system source)) := by
  have result : List.zipWith (fun a b => a+factor*b) (augmentedRow system target) (augmentedRow system source)=
      augmentedRow (materialize (system.applyRowOp (.add target source factor))) target := by
    rw [add_augmentedRow,←augmentedPairs_first system target source,←augmentedPairs_second system target source,
      List.zipWith_map,List.zipWith_self]
  rw [result]
  apply List.ext_getElem (by simp)
  intro index _leftBound _rightBound
  by_cases selected : index=target.val
  · simp [augmentedMatrix,selected]
  · simp [augmentedMatrix,augmentedRow,applyRowOp,RowOp.transform,Fin.ext_iff,selected,Ne.symm selected]

end Counting.StoredGaussian
