import Counting.StoredGaussianIteration

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- Natural counter interface to the original finite pivot enumeration. -/
def pivotAt (state : GaussianState q) (index : Nat) : GaussianState q :=
  if inside : index<q then pivotStep state ⟨index,inside⟩ else state

def pivotCount : Nat → Nat → GaussianState q → GaussianState q
  | _,0,state => state
  | start,count+1,state => pivotCount (start+1) count (pivotAt state start)

@[simp] theorem pivotAt_fin (state : GaussianState q) (pivot : Fin q) :
    pivotAt state pivot.val=pivotStep state pivot := by simp [pivotAt,pivot.isLt]

theorem pivotCount_range (start count : Nat) (state : GaussianState q) :
    pivotCount start count state=(List.range' start count).foldl pivotAt state := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih => simp only [pivotCount,List.range'_succ,List.foldl_cons,ih]

private theorem map_finRange_val (q : Nat) : (List.finRange q).map Fin.val=List.range q := by
  apply List.ext_getElem (by simp)
  intro i leftBound rightBound
  simp

theorem pivotCount_full (state : GaussianState q) :
    pivotCount 0 q state=(List.finRange q).foldl pivotStep state := by
  rw [pivotCount_range,←List.range_eq_range',←map_finRange_val,List.foldl_map]
  have equal : (fun (state : GaussianState q) (pivot : Fin q) => pivotAt state pivot.val)=pivotStep := by
    funext state pivot;exact pivotAt_fin state pivot
  rw [equal]

theorem pivotCount_runGaussian (system : RationalSystem q) :
    pivotCount 0 q ⟨system,[],true⟩=runGaussian system := by
  rw [pivotCount_full]
  simp only [runGaussian,materialize_eq]

theorem pivotCount_add (start first second : Nat) (state : GaussianState q) :
    pivotCount start (first+second) state=pivotCount (start+first) second (pivotCount start first state) := by
  induction first generalizing start state with
  | zero => simp [pivotCount]
  | succ first ih =>
    simp only [Nat.succ_add,pivotCount,ih]
    congr 1

end Counting.StoredGaussian
