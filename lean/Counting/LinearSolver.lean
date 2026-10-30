import Counting.Executable
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace Counting.Executable
open DirectedCounting.VerifiedGaussianAnchorSolver
open DirectedCounting.GaussianGeneratorCompleteness
open scoped Matrix BigOperators

/-- Interpretation of a dense rectangular input system. -/
def rowMatrix (width : Nat) (rows : List Equation) :
    Matrix (Fin rows.length) (Fin width) ℚ :=
  fun i j => (rows.get i).1[j.val]?.getD 0

def rowRhs (rows : List Equation) : Fin rows.length → ℚ :=
  fun i => (rows.get i).2

def RowsSatisfied (width : Nat) (rows : List Equation) (x : Fin width → ℚ) : Prop :=
  ∀ row ∈ rows, (∑ i : Fin width, (row.1[i.val]?.getD 0) * x i) = row.2

def RowsSized (width : Nat) (rows : List Equation) : Prop :=
  ∀ row ∈ rows, row.1.size = width

def vectorArray {width : Nat} (x : Fin width → ℚ) : Array ℚ :=
  ((List.finRange width).map x).toArray

def arrayVector (width : Nat) (x : Array ℚ) : Fin width → ℚ :=
  fun i => x[i.val]?.getD 0

theorem arrayVector_vectorArray {width : Nat} (x : Fin width → ℚ) :
    arrayVector width (vectorArray x) = x := by
  funext i
  simp [arrayVector, vectorArray, ← List.ofFn_eq_map]

theorem vectorArray_size {width : Nat} (x : Fin width → ℚ) :
    (vectorArray x).size = width := by simp [vectorArray]

private theorem sum_map_eq_sum_get {α : Type} (rows : List α) (f : α → ℚ) :
    (rows.map f).sum = ∑ i : Fin rows.length, f (rows.get i) := by
  calc
    (rows.map f).sum = (List.ofFn (fun i => f (rows.get i))).sum := by
      change (rows.map f).sum = (List.ofFn (f ∘ rows.get)).sum
      rw [← List.map_ofFn, List.ofFn_get]
    _ = _ := Fin.sum_ofFn _

theorem normalSystem_coeff (width : Nat) (rows : List Equation) :
    (normalSystem width rows).coeff = (rowMatrix width rows)ᵀ * rowMatrix width rows := by
  funext i j
  simp only [normalSystem, Matrix.mul_apply, Matrix.transpose_apply, rowMatrix]
  exact sum_map_eq_sum_get _ _

theorem normalSystem_rhs (width : Nat) (rows : List Equation) :
    (normalSystem width rows).rhs = (rowMatrix width rows)ᵀ *ᵥ rowRhs rows := by
  funext i
  simp only [normalSystem, Matrix.mulVec, dotProduct, Matrix.transpose_apply, rowMatrix, rowRhs]
  exact sum_map_eq_sum_get _ _

theorem rowsSatisfied_iff (width : Nat) (rows : List Equation) (x : Fin width → ℚ) :
    RowsSatisfied width rows x ↔ rowMatrix width rows *ᵥ x = rowRhs rows := by
  constructor
  · intro h
    funext i
    exact h (rows.get i) (List.get_mem rows i)
  · intro h row hrow
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    subst row
    exact congrFun h i

private theorem rows_check_iff (width : Nat) (rows : List Equation) (x : Fin width → ℚ) :
    (rows.all (fun row =>
      ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0) * x i)).sum == row.2))
      = true ↔ RowsSatisfied width rows x := by
  simp [RowsSatisfied, List.all_eq_true, ← Fin.sum_univ_def]

private theorem sizes_check_iff (width : Nat) (rows : List Equation) :
    (rows.all (fun row => row.1.size == width)) = true ↔ RowsSized width rows := by
  simp [RowsSized, List.all_eq_true]

/-- A replay certificate ending with the identity also certifies uniqueness. -/
theorem verifyTranscript_unique {q : Nat} (system : RationalSystem q)
    (ops : List (RationalSystem.RowOp q)) (x y : Fin q → ℚ)
    (accepted : system.verifyTranscript ops = some x)
    (hy : system.Satisfies y) : y = x := by
  unfold RationalSystem.verifyTranscript at accepted
  dsimp only at accepted
  split at accepted
  next hcheck =>
    have hfinal := (system.replay_satisfies_iff ops hcheck.1 y).mpr hy
    unfold RationalSystem.Satisfies at hfinal
    rw [hcheck.2, Matrix.one_mulVec] at hfinal
    exact hfinal.trans (Option.some.inj accepted)
  next => contradiction

theorem gaussian_unique {q : Nat} (system : RationalSystem q)
    (x y : Fin q → ℚ) (accepted : system.solve? = some x)
    (hy : system.Satisfies y) : y = x := by
  let output := RationalSystem.generate system
  change (if output.generatorSucceeded = true then
    system.verifyTranscript output.transcript else none) = some x at accepted
  split at accepted
  next => exact verifyTranscript_unique system output.transcript x y accepted hy
  next => contradiction

theorem normal_satisfies (width : Nat) (rows : List Equation) (x : Fin width → ℚ)
    (hx : RowsSatisfied width rows x) :
    (normalSystem width rows).Satisfies x := by
  unfold RationalSystem.Satisfies
  rw [normalSystem_coeff, normalSystem_rhs, ← Matrix.mulVec_mulVec,
    (rowsSatisfied_iff width rows x).mp hx]

/-- Extract exactly what the implemented guards and return statement certify. -/
theorem solveLinear_extract (width : Nat) (rows : List Equation) (result : Array ℚ)
    (accepted : solveLinear? width rows = some result) :
    RowsSized width rows ∧ ∃ x : Fin width → ℚ,
      (normalSystem width rows).solve? = some x ∧
      RowsSatisfied width rows x ∧ result = vectorArray x := by
  unfold solveLinear? at accepted
  simp only [Counting.StoredGaussian.solve_eq] at accepted
  split at accepted
  next hbad => contradiction
  next hsize =>
    have hs : RowsSized width rows := (sizes_check_iff width rows).mp (by simpa using hsize)
    cases hsolve : (normalSystem width rows).solve? with
    | none => simp [hsolve] at accepted
    | some x =>
      simp only [hsolve] at accepted
      dsimp only [bind, pure] at accepted
      rw [Option.bind_some] at accepted
      split at accepted
      next hrows =>
        refine ⟨hs, x, rfl, (rows_check_iff width rows x).mp hrows, ?_⟩
        exact (Option.some.inj accepted).symm
      next => contradiction

/-- Returned arrays have the prescribed width and satisfy every original row. -/
theorem solveLinear_sound (width : Nat) (rows : List Equation) (result : Array ℚ)
    (accepted : solveLinear? width rows = some result) :
    RowsSized width rows ∧ result.size = width ∧
      RowsSatisfied width rows (arrayVector width result) := by
  obtain ⟨hs, x, _, hx, rfl⟩ := solveLinear_extract width rows result accepted
  exact ⟨hs, vectorArray_size x, by simpa only [arrayVector_vectorArray] using hx⟩

/-- Any solution of all original rows equals the returned vector. -/
theorem solveLinear_unique (width : Nat) (rows : List Equation) (result : Array ℚ)
    (accepted : solveLinear? width rows = some result)
    (y : Fin width → ℚ) (hy : RowsSatisfied width rows y) :
    y = arrayVector width result := by
  obtain ⟨_, x, hsolve, _, rfl⟩ := solveLinear_extract width rows result accepted
  rw [arrayVector_vectorArray]
  exact gaussian_unique _ x y hsolve (normal_satisfies width rows y hy)

/-- Full column rank and a solution suffice for the exact executable solver. -/
theorem solveLinear_complete (width : Nat) (rows : List Equation)
    (hs : RowsSized width rows) (x : Fin width → ℚ)
    (hx : RowsSatisfied width rows x)
    (hinj : Function.Injective (rowMatrix width rows).mulVec) :
    solveLinear? width rows = some (vectorArray x) := by
  have gramInj : Function.Injective (normalSystem width rows).coeff.mulVec := by
    rw [normalSystem_coeff]
    exact (gram_injective_iff _).mpr hinj
  obtain ⟨y, hy⟩ := generatorCompleteFor_of_coeff_mulVec_injective
    (normalSystem width rows) gramInj
  have equal : x = y := gaussian_unique _ y x hy (normal_satisfies width rows x hx)
  subst y
  have hsize := (sizes_check_iff width rows).mpr hs
  have hrows := (rows_check_iff width rows x).mpr hx
  simp [solveLinear?, hsize, hy, hrows, vectorArray]

/-- Existence and uniqueness of an original solution implies full column rank. -/
theorem rowMatrix_injective_of_unique (width : Nat) (rows : List Equation)
    (x : Fin width → ℚ) (hx : RowsSatisfied width rows x)
    (unique : ∀ y, RowsSatisfied width rows y → y = x) :
    Function.Injective (rowMatrix width rows).mulVec := by
  intro y z hyz
  have hzero : rowMatrix width rows *ᵥ (y-z) = 0 := by
    rw [Matrix.mulVec_sub, hyz, sub_self]
  have hshift : RowsSatisfied width rows (x + (y-z)) := by
    apply (rowsSatisfied_iff width rows _).mpr
    rw [Matrix.mulVec_add, hzero, add_zero]
    exact (rowsSatisfied_iff width rows x).mp hx
  have heq := unique _ hshift
  have hz : y-z = 0 := add_left_cancel (heq.trans (add_zero x).symm)
  exact sub_eq_zero.mp hz

/-- Completeness for the paper's actual condition: a unique rectangular solution. -/
theorem solveLinear_complete_of_unique (width : Nat) (rows : List Equation)
    (hs : RowsSized width rows) (x : Fin width → ℚ)
    (hx : RowsSatisfied width rows x)
    (unique : ∀ y, RowsSatisfied width rows y → y = x) :
    solveLinear? width rows = some (vectorArray x) :=
  solveLinear_complete width rows hs x hx
    (rowMatrix_injective_of_unique width rows x hx unique)

/-- On well-shaped input, rejection means precisely lack of a unique solution. -/
theorem solveLinear_none_iff (width : Nat) (rows : List Equation)
    (hs : RowsSized width rows) :
    solveLinear? width rows = none ↔ ¬ ∃! x, RowsSatisfied width rows x := by
  constructor
  · intro rejected existsUnique
    obtain ⟨x, hx, unique⟩ := existsUnique
    have accepted := solveLinear_complete_of_unique width rows hs x hx unique
    rw [rejected] at accepted
    contradiction
  · intro notUnique
    cases accepted : solveLinear? width rows with
    | none => rfl
    | some result =>
      have correct := solveLinear_sound width rows result accepted
      exact False.elim (notUnique ⟨arrayVector width result, correct.2.2,
        fun y hy => solveLinear_unique width rows result accepted y hy⟩)

private theorem positive_rat_cast (x : ℚ) (hd : x.den = 1) (hp : 0 < x.num) :
    0 < x.num.toNat ∧ (x.num.toNat : ℚ) = x := by
  constructor
  · omega
  · have castInt : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg (by omega)
    have hcast : (x.num.toNat : ℚ) = (x.num : ℚ) := by exact_mod_cast castInt
    exact hcast.trans (Rat.coe_int_num_of_den_eq_one hd)

/-- Accepted conversions preserve every coordinate exactly and return only
strictly positive natural numbers. -/
theorem positiveNaturals_sound (vector : Array ℚ) (result : Array Nat)
    (accepted : positiveNaturals? vector = some result) :
    result.size = vector.size ∧
      ∀ i : Fin vector.size,
        0 < result[i.val]?.getD 0 ∧ ((result[i.val]?.getD 0 : Nat) : ℚ) = vector[i.val] := by
  unfold positiveNaturals? at accepted
  split at accepted
  next hcheck =>
    have hr := (Option.some.inj accepted).symm
    subst result
    refine ⟨by simp, ?_⟩
    intro i
    have hi := (Array.all_eq_true.mp hcheck) i.val i.isLt
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
    simpa [Array.getElem?_eq_getElem, i.isLt] using
      positive_rat_cast vector[i.val] hi.1 hi.2
  next => contradiction

/-- Every strictly positive natural vector passes the exact conversion. -/
theorem positiveNaturals_complete (values : Array Nat)
    (positive : ∀ i : Fin values.size, 0 < values[i.val]) :
    positiveNaturals? (values.map (fun n : Nat => (n : ℚ))) = some values := by
  have check : (values.map (fun n : Nat => (n : ℚ))).all
      (fun x => x.den == 1 && x.num > 0) = true := by
    apply Array.all_eq_true.mpr
    intro i hi
    have hip : i < values.size := by simpa using hi
    simpa [hip] using positive ⟨i, hip⟩
  unfold positiveNaturals?
  rw [if_pos check]
  congr 1
  simp [Array.map_map, Function.comp_def]

/-- Exact characterization of the implementation's integer-positivity guard. -/
theorem positiveNaturals_iff (vector : Array ℚ) (result : Array Nat) :
    positiveNaturals? vector = some result ↔
      result.map (fun n : Nat => (n : ℚ)) = vector ∧
        ∀ i : Fin result.size, 0 < result[i.val] := by
  constructor
  · intro accepted
    obtain ⟨hsize, hcoord⟩ := positiveNaturals_sound vector result accepted
    constructor
    · apply Array.ext
      · simpa using hsize
      · intro i hi hv
        have hir : i < result.size := by simpa using hi
        simpa [hir] using (hcoord ⟨i, hv⟩).2
    · intro i
      have hiv : i.val < vector.size := hsize ▸ i.isLt
      simpa [i.isLt] using (hcoord ⟨i.val, hiv⟩).1
  · rintro ⟨hcast, hp⟩
    rw [← hcast]
    exact positiveNaturals_complete result hp

end Counting.Executable
