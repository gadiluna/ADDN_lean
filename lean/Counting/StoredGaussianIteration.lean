import Counting.StoredGaussian

namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- Total natural-index extension used only to describe the counter-driven
machine loop. On every reached index the bound follows from its counter. -/
def eliminateAt (pivot : Fin q) (state : GaussianState q) (index : Nat) : GaussianState q :=
  if inside : index<q then eliminateOne pivot state ⟨index,inside⟩ else state

def eliminateCount (pivot : Fin q) : Nat → Nat → GaussianState q → GaussianState q
  | _,0,state => state
  | start,count+1,state => eliminateCount pivot (start+1) count (eliminateAt pivot state start)

@[simp] theorem eliminateAt_fin (pivot row : Fin q) (state : GaussianState q) :
    eliminateAt pivot state row.val=eliminateOne pivot state row := by simp [eliminateAt,row.isLt]

@[simp] theorem eliminateAt_ok (pivot : Fin q) (state : GaussianState q) (index : Nat) :
    (eliminateAt pivot state index).ok=state.ok := by
  unfold eliminateAt eliminateOne
  split_ifs <;> rfl

@[simp] theorem eliminateCount_ok (pivot : Fin q) (start count : Nat) (state : GaussianState q) :
    (eliminateCount pivot start count state).ok=state.ok := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih => simp [eliminateCount,ih]

theorem eliminateCount_range (pivot : Fin q) (start count : Nat) (state : GaussianState q) :
    eliminateCount pivot start count state=(List.range' start count).foldl (eliminateAt pivot) state := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih => simp only [eliminateCount,List.range'_succ,List.foldl_cons,ih]

private theorem map_finRange_val (q : Nat) : (List.finRange q).map Fin.val=List.range q := by
  apply List.ext_getElem (by simp)
  intro i leftBound rightBound
  simp

/-- The counter loop visits exactly the original finite row enumeration,
including its skipped pivot row and additions with zero coefficients. -/
theorem eliminateCount_full (pivot : Fin q) (state : GaussianState q) :
    eliminateCount pivot 0 q state=eliminateRows pivot (List.finRange q) state := by
  rw [eliminateCount_range,←List.range_eq_range',←map_finRange_val,List.foldl_map]
  have equal : (fun (state : GaussianState q) (row : Fin q) => eliminateAt pivot state row.val)=
      eliminateOne pivot := by
    funext state row;exact eliminateAt_fin pivot row state
  rw [equal]
  rfl

theorem eliminateCount_add (pivot : Fin q) (start first second : Nat) (state : GaussianState q) :
    eliminateCount pivot start (first+second) state=
      eliminateCount pivot (start+first) second (eliminateCount pivot start first state) := by
  induction first generalizing start state with
  | zero => simp [eliminateCount]
  | succ first ih =>
    simp only [Nat.succ_add,eliminateCount,ih]
    congr 1

theorem eliminateAt_ops_length_le (pivot : Fin q) (state : GaussianState q) (index : Nat) :
    (eliminateAt pivot state index).opsRev.length ≤ state.opsRev.length+1 := by
  unfold eliminateAt eliminateOne
  split_ifs <;> simp [emit]

theorem eliminateCount_ops_length_le (pivot : Fin q) (start count : Nat) (state : GaussianState q) :
    (eliminateCount pivot start count state).opsRev.length ≤ state.opsRev.length+count := by
  induction count generalizing start state with
  | zero => simp [eliminateCount]
  | succ count ih =>
    have next := ih (start+1) (eliminateAt pivot state start)
    have length := eliminateAt_ops_length_le pivot state start
    change (eliminateCount pivot (start+1) count (eliminateAt pivot state start)).opsRev.length ≤ _
    omega

end Counting.StoredGaussian
