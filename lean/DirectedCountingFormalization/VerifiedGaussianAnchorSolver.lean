import DirectedCountingFormalization.ExactAnchorSolver

/-!
# Deterministic Gaussian anchor solver with replay certificates

This file removes determinants from the executed anchor-solver path.  A
Gauss--Jordan generator emits elementary row operations over `ℚ`; an
independent verifier replays the transcript and accepts only if the final
coefficient matrix is the identity.  Soundness therefore does not depend on
the generator implementation.

The generator has a formally bounded number of row operations and a cubic
field-operation cost in the explicit cost model below.  Its pivoting
completeness is proved separately in `GaussianGeneratorCompleteness`.
-/

set_option warningAsError true

namespace DirectedCounting
namespace VerifiedGaussianAnchorSolver

open scoped BigOperators Matrix

variable {q : Nat}

/-- A square rational linear system. -/
structure RationalSystem (q : Nat) where
  coeff : Matrix (Fin q) (Fin q) ℚ
  rhs : Fin q → ℚ

namespace RationalSystem

/-- Elementary row operations used in a replay transcript. -/
inductive RowOp (q : Nat) where
  | swap (i j : Fin q)
  | scale (i : Fin q) (c : ℚ)
  | add (target source : Fin q) (c : ℚ)
deriving DecidableEq, Repr

namespace RowOp

/-- Scaling must be nonzero and a row-addition must use a distinct source. -/
def Valid : RowOp q → Prop
  | .swap _ _ => True
  | .scale _ c => c ≠ 0
  | .add target source _ => target ≠ source

instance (op : RowOp q) : Decidable op.Valid := by
  cases op <;> simp [Valid] <;> infer_instance

/-- Action of a row operation on a column vector. -/
def transform (op : RowOp q) (v : Fin q → ℚ) : Fin q → ℚ :=
  match op with
  | .swap i j => fun r ↦
      if r = i then v j else if r = j then v i else v r
  | .scale i c => fun r ↦ if r = i then c * v i else v r
  | .add target source c => fun r ↦
      if r = target then v target + c * v source else v r

/-- Algebraic inverse of a valid elementary operation. -/
def inverse : RowOp q → RowOp q
  | .swap i j => .swap i j
  | .scale i c => .scale i c⁻¹
  | .add target source c => .add target source (-c)

theorem inverse_transform (op : RowOp q) (valid : op.Valid)
    (v : Fin q → ℚ) :
    op.inverse.transform (op.transform v) = v := by
  funext r
  cases op with
  | swap i j =>
      by_cases hij : i = j
      · subst j
        by_cases hri : r = i
        · subst r
          simp [inverse, transform]
        · simp [inverse, transform, hri]
      · have hji : j ≠ i := Ne.symm hij
        by_cases hri : r = i
        · subst r
          simp [inverse, transform, hji]
        · by_cases hrj : r = j
          · subst r
            simp [inverse, transform, hji]
          · simp [inverse, transform, hri, hrj]
  | scale i c =>
      by_cases hri : r = i
      · subst r
        simp only [Valid] at valid
        simp [inverse, transform, valid]
      · simp [inverse, transform, hri]
  | add target source c =>
      simp only [Valid] at valid
      by_cases hrt : r = target
      · subst r
        have hst : source ≠ target := Ne.symm valid
        simp [inverse, transform, hst]
      · simp [inverse, transform, hrt]

theorem transform_injective (op : RowOp q) (valid : op.Valid) :
    Function.Injective op.transform := by
  intro v w hvw
  rw [← op.inverse_transform valid v, ← op.inverse_transform valid w, hvw]

end RowOp

variable (S : RationalSystem q)

/-- Apply one elementary operation to both sides of the system. -/
def applyRowOp (op : RowOp q) : RationalSystem q where
  coeff := fun r c ↦ op.transform (fun i ↦ S.coeff i c) r
  rhs := op.transform S.rhs

theorem applyRowOp_mulVec (op : RowOp q) (x : Fin q → ℚ) :
    (S.applyRowOp op).coeff *ᵥ x = op.transform (S.coeff *ᵥ x) := by
  funext r
  cases op with
  | swap i j =>
      by_cases hri : r = i <;> by_cases hrj : r = j <;>
        simp [applyRowOp, RowOp.transform, Matrix.mulVec, dotProduct, hri, hrj]
  | scale i c =>
      by_cases hri : r = i
      · subst r
        simp only [applyRowOp, RowOp.transform, if_pos, Matrix.mulVec,
          dotProduct]
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]
      · simp [applyRowOp, RowOp.transform, Matrix.mulVec, dotProduct, hri]
  | add target source c =>
      by_cases hrt : r = target
      · subst r
        simp only [applyRowOp, RowOp.transform, if_pos, Matrix.mulVec,
          dotProduct]
        simp_rw [add_mul, mul_assoc]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      · simp [applyRowOp, RowOp.transform, Matrix.mulVec, dotProduct, hrt]

/-- A vector satisfies a system. -/
def Satisfies (x : Fin q → ℚ) : Prop := S.coeff *ᵥ x = S.rhs

theorem applyRowOp_satisfies_iff (op : RowOp q) (valid : op.Valid)
    (x : Fin q → ℚ) :
    (S.applyRowOp op).Satisfies x ↔ S.Satisfies x := by
  unfold Satisfies
  rw [S.applyRowOp_mulVec]
  change op.transform (S.coeff *ᵥ x) = op.transform S.rhs ↔ _
  exact (op.transform_injective valid).eq_iff

/-- Replay a row-operation transcript. -/
def replay : RationalSystem q → List (RowOp q) → RationalSystem q
  | state, [] => state
  | state, op :: ops => replay (state.applyRowOp op) ops

def TranscriptValid (ops : List (RowOp q)) : Prop :=
  ops.Forall RowOp.Valid

instance (ops : List (RowOp q)) : Decidable (TranscriptValid ops) := by
  unfold TranscriptValid
  infer_instance

theorem replay_satisfies_iff (ops : List (RowOp q))
    (valid : TranscriptValid ops) (x : Fin q → ℚ) :
    (replay S ops).Satisfies x ↔ S.Satisfies x := by
  induction ops generalizing S with
  | nil => simp [replay]
  | cons op ops ih =>
      simp only [TranscriptValid, List.forall_cons] at valid
      rw [replay, ih (S := S.applyRowOp op) valid.2,
        S.applyRowOp_satisfies_iff op valid.1]

/-- Independently replay a transcript and return its transformed right-hand
side only if every operation is valid and the final matrix is the identity. -/
def verifyTranscript (ops : List (RowOp q)) : Option (Fin q → ℚ) :=
  let final := replay S ops
  if TranscriptValid ops ∧ final.coeff = 1 then some final.rhs else none

/-- Replay soundness: every returned vector solves the original system. -/
theorem verifyTranscript_sound (ops : List (RowOp q)) (x : Fin q → ℚ)
    (accepted : S.verifyTranscript ops = some x) :
    S.Satisfies x := by
  let final := replay S ops
  change (if TranscriptValid ops ∧ final.coeff = 1 then
    some final.rhs else none) = some x at accepted
  by_cases hcheck : TranscriptValid ops ∧ final.coeff = 1
  · rw [if_pos hcheck] at accepted
    have hx : (replay S ops).rhs = x := by
      simpa only [final, Option.some.injEq] using accepted
    have hcoeff : (replay S ops).coeff = 1 := by
      simpa only [final] using hcheck.2
    have hfinal : (replay S ops).Satisfies x := by
      unfold Satisfies
      rw [hcoeff, Matrix.one_mulVec, hx]
    exact ((S.replay_satisfies_iff ops hcheck.1 x).mp hfinal)
  · rw [if_neg hcheck] at accepted
    simp at accepted

/-! ## Deterministic Gauss--Jordan transcript generator -/

/-- Internal generator state.  Operations are stored in reverse order so
emission is constant time. -/
structure GaussianState (q : Nat) where
  system : RationalSystem q
  opsRev : List (RowOp q)
  ok : Bool

namespace GaussianState

/-- Emit and execute one row operation. -/
def emit (state : GaussianState q) (op : RowOp q) : GaussianState q where
  system := state.system.applyRowOp op
  opsRev := op :: state.opsRev
  ok := state.ok

def fail (state : GaussianState q) : GaussianState q :=
  { state with ok := false }

theorem emit_opsRev_length (state : GaussianState q) (op : RowOp q) :
    (state.emit op).opsRev.length = state.opsRev.length + 1 := by
  simp [emit]

end GaussianState

/-- Least available pivot row at or below the current diagonal position. -/
def findPivot? (system : RationalSystem q) (pivot : Fin q) : Option (Fin q) :=
  (List.finRange q).find? fun row ↦
    decide (pivot.1 ≤ row.1 ∧ system.coeff row pivot ≠ 0)

/-- Eliminate one nonpivot row. -/
def eliminateOne (pivot : Fin q) (state : GaussianState q)
    (row : Fin q) : GaussianState q :=
  if state.ok then
    if row = pivot then state
    else state.emit (.add row pivot (-state.system.coeff row pivot))
  else state

/-- Eliminate the pivot column in a supplied finite row list. -/
def eliminateRows (pivot : Fin q) (rows : List (Fin q))
    (state : GaussianState q) : GaussianState q :=
  rows.foldl (eliminateOne pivot) state

/-- One deterministic pivot/normalize/eliminate stage. -/
def pivotStep (state : GaussianState q) (pivot : Fin q) : GaussianState q :=
  if state.ok then
    match findPivot? state.system pivot with
    | none => state.fail
    | some row =>
        let swapped := state.emit (.swap pivot row)
        let pivotValue := swapped.system.coeff pivot pivot
        if pivotValue = 0 then swapped.fail
        else
          let normalized := swapped.emit (.scale pivot pivotValue⁻¹)
          eliminateRows pivot (List.finRange q) normalized
  else state

/-- Run all diagonal stages. -/
def runGaussian (system : RationalSystem q) : GaussianState q :=
  (List.finRange q).foldl pivotStep
    { system := system, opsRev := [], ok := true }

/-- Public data-only output of the generator. -/
structure GaussianOutput (q : Nat) where
  transcript : List (RowOp q)
  candidate : Fin q → ℚ
  generatorSucceeded : Bool

def generate (system : RationalSystem q) : GaussianOutput q :=
  let final := runGaussian system
  { transcript := final.opsRev.reverse
    candidate := final.system.rhs
    generatorSucceeded := final.ok }

/-- The executed solve path trusts only transcript replay, not the stored
candidate or success flag. -/
def solve? (system : RationalSystem q) : Option (Fin q → ℚ) :=
  let output := generate system
  if output.generatorSucceeded then
    system.verifyTranscript output.transcript
  else none

theorem solve?_sound (system : RationalSystem q) (x : Fin q → ℚ)
    (accepted : solve? system = some x) :
    system.Satisfies x := by
  let output := generate system
  change (if output.generatorSucceeded = true then
    system.verifyTranscript output.transcript else none) = some x at accepted
  by_cases hsuccess : output.generatorSucceeded = true
  · rw [if_pos hsuccess] at accepted
    exact system.verifyTranscript_sound output.transcript x accepted
  · rw [if_neg hsuccess] at accepted
    simp at accepted

/-! ## Formal operation-count bound -/

theorem eliminateOne_opsRev_length_le
    (pivot row : Fin q) (state : GaussianState q) :
    (eliminateOne pivot state row).opsRev.length ≤
      state.opsRev.length + 1 := by
  by_cases hok : state.ok = true
  · by_cases hrow : row = pivot
    · simp [eliminateOne, hok, hrow]
    · simp [eliminateOne, hok, hrow, GaussianState.emit]
  · simp [eliminateOne, hok]

theorem eliminateRows_opsRev_length_le
    (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q) :
    (eliminateRows pivot rows state).opsRev.length ≤
      state.opsRev.length + rows.length := by
  induction rows generalizing state with
  | nil => simp [eliminateRows]
  | cons row rows ih =>
      have hstep := eliminateOne_opsRev_length_le pivot row state
      have htail := ih (state := eliminateOne pivot state row)
      change (eliminateRows pivot rows (eliminateOne pivot state row)).opsRev.length ≤
        state.opsRev.length + (row :: rows).length
      calc
        _ ≤ (eliminateOne pivot state row).opsRev.length + rows.length :=
          htail
        _ ≤ (state.opsRev.length + 1) + rows.length :=
          Nat.add_le_add_right hstep _
        _ = state.opsRev.length + (row :: rows).length := by simp; omega

theorem pivotStep_opsRev_length_le
    (state : GaussianState q) (pivot : Fin q) :
    (pivotStep state pivot).opsRev.length ≤
      state.opsRev.length + (q + 2) := by
  by_cases hok : state.ok = true
  · cases hpivot : findPivot? state.system pivot with
    | none =>
        simp [pivotStep, hok, hpivot, GaussianState.fail]
    | some row =>
        let swapped := state.emit (.swap pivot row)
        by_cases hvalue : swapped.system.coeff pivot pivot = 0
        · simp only [pivotStep, hok, if_true, hpivot, swapped, hvalue]
          simp [GaussianState.fail, GaussianState.emit]
        · let normalized := swapped.emit
              (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
          have heliminate := eliminateRows_opsRev_length_le pivot
            (List.finRange q) normalized
          have hnormalized : normalized.opsRev.length =
              state.opsRev.length + 2 := by
            simp [normalized, swapped, GaussianState.emit]
          simp only [pivotStep, hok, if_true, hpivot, swapped, hvalue,
            if_false]
          change (eliminateRows pivot (List.finRange q) normalized).opsRev.length ≤
            state.opsRev.length + (q + 2)
          simp only [List.length_finRange] at heliminate
          omega
  · simp [pivotStep, hok]

/-- Generic accumulation of the per-pivot transcript bound. -/
theorem foldl_pivotStep_opsRev_length_le
    (pivots : List (Fin q)) (state : GaussianState q) :
    (pivots.foldl pivotStep state).opsRev.length ≤
      state.opsRev.length + pivots.length * (q + 2) := by
  induction pivots generalizing state with
  | nil => simp
  | cons pivot pivots ih =>
      have hstep := pivotStep_opsRev_length_le state pivot
      have htail := ih (state := pivotStep state pivot)
      simp only [List.foldl_cons, List.length_cons]
      calc
        ((pivot :: pivots).foldl pivotStep state).opsRev.length =
            (pivots.foldl pivotStep (pivotStep state pivot)).opsRev.length := rfl
        _ ≤ (pivotStep state pivot).opsRev.length +
            pivots.length * (q + 2) := htail
        _ ≤ (state.opsRev.length + (q + 2)) +
            pivots.length * (q + 2) :=
          Nat.add_le_add_right hstep _
        _ = state.opsRev.length + (pivots.length + 1) * (q + 2) := by
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- At most `q * (q + 2)` elementary operations are emitted. -/
theorem runGaussian_opsRev_length_le (system : RationalSystem q) :
    (runGaussian system).opsRev.length ≤ q * (q + 2) := by
  have h := foldl_pivotStep_opsRev_length_le (List.finRange q)
    ({ system := system, opsRev := [], ok := true } : GaussianState q)
  simpa [runGaussian] using h

theorem generate_transcript_length_le (system : RationalSystem q) :
    (generate system).transcript.length ≤ q * (q + 2) := by
  simpa [generate] using runGaussian_opsRev_length_le system

namespace RowOp

/-- Exact field-operation model for executing one augmented row operation.
The reciprocal used by scaling and the negation used by row addition are
included.  Row swaps use no field arithmetic. -/
def fieldOperationCost : RowOp q → Nat
  | .swap _ _ => 0
  | .scale _ _ => q + 2
  | .add _ _ _ => 2 * (q + 1) + 1

theorem fieldOperationCost_le (op : RowOp q) :
    op.fieldOperationCost ≤ 3 * (q + 1) := by
  cases op with
  | swap => simp [fieldOperationCost]
  | scale => simp [fieldOperationCost]; omega
  | add => simp [fieldOperationCost]

end RowOp

def transcriptFieldOperationCost (ops : List (RowOp q)) : Nat :=
  (ops.map RowOp.fieldOperationCost).sum

theorem transcriptFieldOperationCost_reverse (ops : List (RowOp q)) :
    transcriptFieldOperationCost ops.reverse =
      transcriptFieldOperationCost ops := by
  simp [transcriptFieldOperationCost]

theorem transcriptFieldOperationCost_le (ops : List (RowOp q)) :
    transcriptFieldOperationCost ops ≤
      ops.length * (3 * (q + 1)) := by
  induction ops with
  | nil => simp [transcriptFieldOperationCost]
  | cons op ops ih =>
      unfold transcriptFieldOperationCost at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hop := RowOp.fieldOperationCost_le op
      calc
        op.fieldOperationCost + (ops.map RowOp.fieldOperationCost).sum ≤
            3 * (q + 1) + ops.length * (3 * (q + 1)) :=
          Nat.add_le_add hop ih
        _ = (ops.length + 1) * (3 * (q + 1)) := by
          simp [Nat.add_mul, Nat.add_comm]

/-- Explicit cubic field-operation bound. -/
def gaussianFieldOperationBound (q : Nat) : Nat :=
  q * (q + 2) * (3 * (q + 1))

theorem generate_fieldOperationCost_le (system : RationalSystem q) :
    transcriptFieldOperationCost (generate system).transcript ≤
      gaussianFieldOperationBound q := by
  calc
    transcriptFieldOperationCost (generate system).transcript ≤
        (generate system).transcript.length * (3 * (q + 1)) :=
      transcriptFieldOperationCost_le _
    _ ≤ (q * (q + 2)) * (3 * (q + 1)) :=
      Nat.mul_le_mul_right _ (generate_transcript_length_le system)
    _ = gaussianFieldOperationBound q := rfl

theorem gaussianFieldOperationBound_le_cubic (q : Nat) :
    gaussianFieldOperationBound q ≤ 3 * (q + 2) ^ 3 := by
  unfold gaussianFieldOperationBound
  have hq : q ≤ q + 2 := by omega
  have hqOne : q + 1 ≤ q + 2 := by omega
  calc
    q * (q + 2) * (3 * (q + 1)) ≤
        (q + 2) * (q + 2) * (3 * (q + 2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq (Nat.le_refl _))
        (Nat.mul_le_mul_left 3 hqOne)
    _ = 3 * (q + 2) ^ 3 := by ring

end RationalSystem

/-! ## Specialization to the normalized anchor system -/

/-- Determinant-free presentation of the normal equations constructed in
`ExactAnchorSolver`. -/
def anchorSystem (A : IntegralAnchorInstance q) : RationalSystem q where
  coeff := ExactAnchorSolver.normalMatrix A
  rhs := ExactAnchorSolver.normalizedRhs A

def solveAnchor? (A : IntegralAnchorInstance q) : Option (Fin q → ℚ) :=
  RationalSystem.solve? (anchorSystem A)

theorem solveAnchor?_sound (A : IntegralAnchorInstance q) (x : Fin q → ℚ)
    (accepted : solveAnchor? A = some x) :
    ExactAnchorSolver.normalMatrix A *ᵥ x =
      ExactAnchorSolver.normalizedRhs A := by
  exact RationalSystem.solve?_sound (anchorSystem A) x accepted

/-- If a valid positive integral anchor exists, every rational vector
accepted by Gaussian replay is exactly that normalized anchor. -/
theorem solveAnchor?_eq_natCast_of_some
    {candidate : Nat}
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) (x : Fin q → ℚ)
    (accepted : solveAnchor? A = some x) :
    x = fun i ↦ (output.weight i : ℚ) := by
  apply ExactAnchorSolver.normalMatrix_mulVec_injective A output valid
  rw [solveAnchor?_sound A x accepted,
    ExactAnchorSolver.normalMatrix_mulVec_natCast_eq_rhs A output valid]

/-- Gaussian rational solve followed by the independently verified integral
conversion. -/
def solveAnchorNat? (A : IntegralAnchorInstance q) :
    Option (Fin q → Nat) :=
  (solveAnchor? A).bind ExactAnchorSolver.rationalVectorToNat?

theorem solveAnchorNat?_eq_of_some
    {candidate : Nat}
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) (weight : Fin q → Nat)
    (accepted : solveAnchorNat? A = some weight) :
    weight = output.weight := by
  cases hsolve : solveAnchor? A with
  | none =>
      simp [solveAnchorNat?, hsolve] at accepted
  | some x =>
      have hx := solveAnchor?_eq_natCast_of_some A output valid x hsolve
      unfold solveAnchorNat? at accepted
      rw [hsolve, hx] at accepted
      simp only [Option.bind_some] at accepted
      rw [ExactAnchorSolver.rationalVectorToNat?_natCast] at accepted
      exact (Option.some.inj accepted).symm

/-!
## Interface to generator completeness

The executed path, replay soundness, integral conversion, and cubic operation
bound are proved above.  The proposition below is the interface discharged
for every injective matrix, and hence every valid anchor, by
`GaussianGeneratorCompleteness`.  Soundness remains independent of that
generator proof because every output is accepted only after transcript replay.
-/

/-- Named statement of the generator-completeness property. -/
def GeneratorCompleteFor (system : RationalSystem q) : Prop :=
  ∃ x, RationalSystem.solve? system = some x

end VerifiedGaussianAnchorSolver
end DirectedCounting
