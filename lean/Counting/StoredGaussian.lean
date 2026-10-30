import DirectedCountingFormalization.GaussianGeneratorCompleteness

/-! Materialized exact Gaussian elimination. Every elementary operation
stores all matrix and right-hand-side entries in arrays. This prevents a
chain of functional row updates from repeatedly recomputing earlier values.
The generator and independent transcript verifier are both materialized;
their results equal the already verified mathematical implementations. -/
namespace Counting.StoredGaussian
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem

variable {q : Nat}

/-- Evaluate each coefficient once and retain its value in a dense array. -/
def materialize (system : RationalSystem q) : RationalSystem q :=
  let matrix := Array.ofFn (fun i : Fin q => Array.ofFn (system.coeff i))
  let vector := Array.ofFn system.rhs
  { coeff := fun i j => (matrix[i.val]?.getD #[])[j.val]?.getD 0
    rhs := fun i => vector[i.val]?.getD 0 }

@[simp] theorem materialize_eq (system : RationalSystem q) : materialize system = system := by
  cases system
  simp [materialize]

def emit (state : GaussianState q) (op : RowOp q) : GaussianState q :=
  { state with system := materialize (state.system.applyRowOp op), opsRev := op :: state.opsRev }

@[simp] theorem emit_eq (state : GaussianState q) (op : RowOp q) :
    emit state op = state.emit op := by simp [emit, GaussianState.emit]

def eliminateOne (pivot : Fin q) (state : GaussianState q) (row : Fin q) : GaussianState q :=
  if state.ok then
    if row = pivot then state
    else emit state (.add row pivot (-state.system.coeff row pivot))
  else state

@[simp] theorem eliminateOne_eq (pivot : Fin q) (state : GaussianState q) (row : Fin q) :
    eliminateOne pivot state row = RationalSystem.eliminateOne pivot state row := by
  simp [eliminateOne, RationalSystem.eliminateOne]

def eliminateRows (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q) : GaussianState q :=
  rows.foldl (eliminateOne pivot) state

@[simp] theorem eliminateRows_eq (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q) :
    eliminateRows pivot rows state = RationalSystem.eliminateRows pivot rows state := by
  have equal : eliminateOne pivot = RationalSystem.eliminateOne pivot :=
    funext (fun state => funext (fun row => eliminateOne_eq pivot state row))
  rw [eliminateRows, RationalSystem.eliminateRows, equal]

def pivotStep (state : GaussianState q) (pivot : Fin q) : GaussianState q :=
  if state.ok then
    match findPivot? state.system pivot with
    | none => state.fail
    | some row =>
        let swapped := emit state (.swap pivot row)
        let value := swapped.system.coeff pivot pivot
        if value = 0 then swapped.fail
        else eliminateRows pivot (List.finRange q) (emit swapped (.scale pivot value⁻¹))
  else state

@[simp] theorem pivotStep_eq (state : GaussianState q) (pivot : Fin q) :
    pivotStep state pivot = RationalSystem.pivotStep state pivot := by
  simp only [pivotStep, RationalSystem.pivotStep, emit_eq, eliminateRows_eq]
  rfl

def runGaussian (system : RationalSystem q) : GaussianState q :=
  (List.finRange q).foldl pivotStep { system := materialize system, opsRev := [], ok := true }

@[simp] theorem runGaussian_eq (system : RationalSystem q) :
    runGaussian system = RationalSystem.runGaussian system := by
  have equal : (pivotStep : GaussianState q → Fin q → GaussianState q) = RationalSystem.pivotStep :=
    funext (fun state => funext (fun pivot => pivotStep_eq state pivot))
  simp only [runGaussian, RationalSystem.runGaussian, materialize_eq, equal]

def replay (system : RationalSystem q) : List (RowOp q) → RationalSystem q
  | [] => system
  | op :: ops => replay (materialize (system.applyRowOp op)) ops

@[simp] theorem replay_eq (system : RationalSystem q) (ops : List (RowOp q)) :
    replay system ops = system.replay ops := by
  induction ops generalizing system with
  | nil => rfl
  | cons op ops ih => simp only [replay, RationalSystem.replay, materialize_eq, ih]

def verifyTranscript (system : RationalSystem q) (ops : List (RowOp q)) : Option (Fin q → ℚ) :=
  let final := replay (materialize system) ops
  if TranscriptValid ops ∧ final.coeff = 1 then some final.rhs else none

@[simp] theorem verifyTranscript_eq (system : RationalSystem q) (ops : List (RowOp q)) :
    verifyTranscript system ops = system.verifyTranscript ops := by
  simp only [verifyTranscript, RationalSystem.verifyTranscript, materialize_eq, replay_eq]

def solve? (system : RationalSystem q) : Option (Fin q → ℚ) :=
  let final := runGaussian system
  if final.ok then verifyTranscript system final.opsRev.reverse else none

/-- Both successful answers and every rejected system are unchanged. -/
@[simp] theorem solve_eq (system : RationalSystem q) : solve? system = system.solve? := by
  simp only [solve?, RationalSystem.solve?, RationalSystem.generate, runGaussian_eq, verifyTranscript_eq]

/-- The materialized generator retains the established transcript bound. -/
theorem transcript_length_le (system : RationalSystem q) :
    (runGaussian system).opsRev.length ≤ q * (q+2) := by
  rw [runGaussian_eq]
  exact runGaussian_opsRev_length_le system

end Counting.StoredGaussian
