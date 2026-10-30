import Counting.LinearSolver
import Counting.LabelBoundsAnchor
import Counting.GaussianMinorBounds

/-! Bounds for the actual normal equations passed to the stored Gaussian
solver. Integrality is preserved by the rectangular-to-square conversion;
the sum of products increases coefficient lengths only polynomially. -/
namespace Counting.GaussianBits
open Counting.Executable
open scoped BigOperators Matrix

def integerNormalCoeff (width : Nat) (rows : List Equation) :
    Matrix (Fin width) (Fin width) ℤ :=
  fun i j => ∑ r : Fin rows.length,
    (rowMatrix width rows r i).num * (rowMatrix width rows r j).num

def integerNormalRhs (width : Nat) (rows : List Equation) : Fin width → ℤ :=
  fun i => ∑ r : Fin rows.length,
    (rowMatrix width rows r i).num * (rowRhs rows r).num

theorem normal_coeff_cast (width : Nat) (rows : List Equation)
    (integral : ∀ r i, (rowMatrix width rows r i).den = 1) :
    (normalSystem width rows).coeff = (integerNormalCoeff width rows).map (Int.cast : ℤ → ℚ) := by
  rw [normalSystem_coeff]
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    integerNormalCoeff, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Rat.coe_int_num_of_den_eq_one (integral r i),
    Rat.coe_int_num_of_den_eq_one (integral r j)]

theorem normal_rhs_cast (width : Nat) (rows : List Equation)
    (coeffIntegral : ∀ r i, (rowMatrix width rows r i).den = 1)
    (rhsIntegral : ∀ r, (rowRhs rows r).den = 1) :
    (normalSystem width rows).rhs = fun i => (integerNormalRhs width rows i : ℚ) := by
  rw [normalSystem_rhs]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    integerNormalRhs, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Rat.coe_int_num_of_den_eq_one (coeffIntegral r i),
    Rat.coe_int_num_of_den_eq_one (rhsIntegral r)]

theorem sum_products_natAbs_le {ι : Type} [Fintype ι] (a b : ι → ℤ) (M : Nat)
    (left : ∀ i, (a i).natAbs ≤ M) (right : ∀ i, (b i).natAbs ≤ M) :
    (∑ i, a i * b i).natAbs ≤ Fintype.card ι * M^2 := by
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, M*M := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (left i) (right i)
    _ = _ := by simp [pow_two]

theorem integer_normal_bounds (width : Nat) (rows : List Equation) (M : Nat)
    (coeffBound : ∀ r i, (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhsBound : ∀ r, (rowRhs rows r).num.natAbs ≤ M) :
    (∀ i j, (integerNormalCoeff width rows i j).natAbs ≤ rows.length*M^2) ∧
    (∀ i, (integerNormalRhs width rows i).natAbs ≤ rows.length*M^2) := by
  constructor
  · intro i j
    simpa only [integerNormalCoeff, Fintype.card_fin] using
      sum_products_natAbs_le (fun r => (rowMatrix width rows r i).num)
        (fun r => (rowMatrix width rows r j).num) M (fun r => coeffBound r i)
        (fun r => coeffBound r j)
  · intro i
    simpa only [integerNormalRhs, Fintype.card_fin] using
      sum_products_natAbs_le (fun r => (rowMatrix width rows r i).num)
        (fun r => (rowRhs rows r).num) M (fun r => coeffBound r i) rhsBound

theorem normal_envelope_bits (count M : Nat) :
    (count*M^2).size ≤ count.size + 2*M.size + 1 := by
  have bound : count*M^2 ≤ 2^(count.size+2*M.size) := by
    calc
      _ ≤ 2^count.size * (2^M.size)^2 :=
        Nat.mul_le_mul (Nat.lt_size_self count).le
          (Nat.pow_le_pow_left (Nat.lt_size_self M).le 2)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  simpa only [Nat.size_pow] using Nat.size_le_size bound

theorem normal_system_bits (width : Nat) (rows : List Equation) (M : Nat)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧
      (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M) :
    (∀ i j, ((normalSystem width rows).coeff i j).den = 1 ∧
      ((normalSystem width rows).coeff i j).num.natAbs.size ≤
        rows.length.size + 2*M.size + 1) ∧
    (∀ i, ((normalSystem width rows).rhs i).den = 1 ∧
      ((normalSystem width rows).rhs i).num.natAbs.size ≤
        rows.length.size + 2*M.size + 1) := by
  obtain ⟨left, right⟩ := integer_normal_bounds width rows M
    (fun r i => (coeff r i).2) (fun r => (rhs r).2)
  rw [normal_coeff_cast width rows (fun r i => (coeff r i).1),
    normal_rhs_cast width rows (fun r i => (coeff r i).1) (fun r => (rhs r).1)]
  constructor
  · intro i j
    simp only [Matrix.map_apply, Rat.den_intCast, Rat.num_intCast, true_and]
    exact (Nat.size_le_size (left i j)).trans (normal_envelope_bits _ _)
  · intro i
    simp only [Rat.den_intCast, Rat.num_intCast, true_and]
    exact (Nat.size_le_size (right i)).trans (normal_envelope_bits _ _)

theorem lookup_integral_bounded (values : Array ℚ) (M index : Nat)
    (bounded : ∀ value ∈ values.toList, value.den = 1 ∧ value.num.natAbs ≤ M) :
    (values[index]?.getD 0).den = 1 ∧ (values[index]?.getD 0).num.natAbs ≤ M := by
  cases found : values[index]? with
  | none => simp
  | some value =>
      simp only [Option.getD_some]
      exact bounded value (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))

/-- Bound all entries of the actual anchor rows, including the default
zero returned by an out-of-range array lookup. -/
theorem anchor_rows_integral_bounded (vista : Vista) (anchor leaders M width : Nat)
    (degrees : ∀ i, i < vista.nodes.size → (vista.node i).degree ≤ M)
    (reds : ∀ i, i < vista.nodes.size → ∀ old, countFrom (vista.node i) old ≤ M) :
    (∀ r i, (rowMatrix width (anchorRows vista anchor leaders) r i).den = 1 ∧
      (rowMatrix width (anchorRows vista anchor leaders) r i).num.natAbs ≤
        max (max (2*M) 1) leaders) ∧
    (∀ r, (rowRhs (anchorRows vista anchor leaders) r).den = 1 ∧
      (rowRhs (anchorRows vista anchor leaders) r).num.natAbs ≤ max (max (2*M) 1) leaders) := by
  constructor
  · intro r i
    apply lookup_integral_bounded
    intro value present
    obtain ⟨integral, bounded, _⟩ := anchorRows_coefficients vista anchor leaders M degrees reds _
      (List.get_mem _ r) value present
    exact ⟨integral, bounded.trans (le_max_left _ _)⟩
  · intro r
    obtain ⟨integral, bounded, _⟩ := anchorRows_rhs vista anchor leaders _ (List.get_mem _ r)
    exact ⟨integral, bounded.trans (le_max_right _ _)⟩

theorem anchor_normal_system_bits (vista : Vista) (anchor leaders M width : Nat)
    (degrees : ∀ i, i < vista.nodes.size → (vista.node i).degree ≤ M)
    (reds : ∀ i, i < vista.nodes.size → ∀ old, countFrom (vista.node i) old ≤ M) :
    (∀ i j, ((normalSystem width (anchorRows vista anchor leaders)).coeff i j).den = 1 ∧
      ((normalSystem width (anchorRows vista anchor leaders)).coeff i j).num.natAbs.size ≤
        (anchorRows vista anchor leaders).length.size + 2*(max (max (2*M) 1) leaders).size + 1) ∧
    (∀ i, ((normalSystem width (anchorRows vista anchor leaders)).rhs i).den = 1 ∧
      ((normalSystem width (anchorRows vista anchor leaders)).rhs i).num.natAbs.size ≤
        (anchorRows vista anchor leaders).length.size + 2*(max (max (2*M) 1) leaders).size + 1) := by
  obtain ⟨coeff, rhs⟩ := anchor_rows_integral_bounded vista anchor leaders M width degrees reds
  exact normal_system_bits width _ _ coeff rhs

end Counting.GaussianBits
