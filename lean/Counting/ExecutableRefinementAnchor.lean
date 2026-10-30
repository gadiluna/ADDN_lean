import Counting.ExecutableRefinementAudit
import Counting.ExecutableRefinementWeights
import Counting.TimingProtocolAudit

namespace Counting.Executable
open scoped BigOperators

def NodeAnchorSolution (vista : Vista) (anchor leaders : Nat) (z : Nat → ℚ) : Prop :=
  (∀ old ∈ levelNodes vista (anchor - 1),
    ((levelNodes vista anchor).map (fun i => (countFrom (vista.node i) old : ℚ) * z i)).sum =
      ((levelNodes vista anchor).map (fun i =>
        if (vista.node i).parent = some old then (vista.node i).degree * z i else 0)).sum) ∧
  ((levelNodes vista anchor).map (fun i => if (vista.node i).leader then z i else 0)).sum = leaders

theorem sum_list_coordinates {M : Type*} [AddCommMonoid M] (nodes : List Nat) (f : Nat → M) :
    (∑ j : Fin nodes.length, f nodes[j.val]) = (nodes.map f).sum := by
  have equality : List.ofFn (fun j : Fin nodes.length => f nodes[j.val]) = nodes.map f := by
    change List.ofFn (f ∘ nodes.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← List.sum_ofFn, equality]

theorem equation_coordinate_sum (nodes : List Nat) (coeff z : Nat → ℚ) :
    (∑ j : Fin nodes.length, ((nodes.map coeff).toArray[j.val]?.getD 0) * z nodes[j.val]) =
      (nodes.map (fun i => coeff i * z i)).sum := by
  rw [← sum_list_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem j.isLt,
    Option.map_some, Option.getD_some]

theorem list_sum_map_sub (nodes : List Nat) (f g : Nat → ℚ) :
    (nodes.map (fun i => f i - g i)).sum = (nodes.map f).sum - (nodes.map g).sum := by
  induction nodes with
  | nil => simp
  | cons i rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem anchorRows_sized (vista : Vista) (anchor leaders : Nat) :
    RowsSized (levelNodes vista anchor).length (anchorRows vista anchor leaders) := by
  intro row present
  simp only [anchorRows, List.mem_append, List.mem_map, List.mem_singleton] at present
  rcases present with ⟨old, _, rfl⟩ | rfl <;> simp

theorem anchorRows_satisfied_iff (vista : Vista) (anchor leaders : Nat) (z : Nat → ℚ) :
    RowsSatisfied (levelNodes vista anchor).length (anchorRows vista anchor leaders)
      (fun j => z (levelNodes vista anchor)[j.val]) ↔ NodeAnchorSolution vista anchor leaders z := by
  constructor
  · intro rows
    constructor
    · intro old present
      have eq := rows _ (List.mem_append_left _ (List.mem_map.mpr ⟨old, present, rfl⟩))
      dsimp only at eq
      rw [equation_coordinate_sum] at eq
      simp only [beq_iff_eq, sub_mul, apply_ite (fun n : Nat => (n : ℚ)), Nat.cast_zero, ite_mul, zero_mul, list_sum_map_sub] at eq
      exact sub_eq_zero.mp eq
    · have eq := rows _ (List.mem_append_right _ (List.mem_singleton_self _))
      dsimp only at eq
      rw [equation_coordinate_sum] at eq
      simpa only [ite_mul, one_mul, zero_mul] using eq
  · intro solution row present
    simp only [anchorRows, List.mem_append, List.mem_map, List.mem_singleton] at present
    rcases present with ⟨old, present, rfl⟩ | rfl
    · rw [equation_coordinate_sum]
      simp only [beq_iff_eq, sub_mul, apply_ite (fun n : Nat => (n : ℚ)), Nat.cast_zero, ite_mul, zero_mul, list_sum_map_sub]
      exact sub_eq_zero.mpr (solution.1 old present)
    · rw [equation_coordinate_sum]
      simpa only [ite_mul, one_mul, zero_mul] using solution.2


theorem AuditExtracted.anchor_coordinate {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural)
    (j : Fin (levelNodes vista witness.anchor).length) :
    (witness.weights[(levelNodes vista witness.anchor)[j.val]]?.getD 0 : ℚ) =
      arrayVector (levelNodes vista witness.anchor).length values j := by
  have dimensions := (solveLinear_sound _ _ _ evidence.solved).2.1
  have exactNatural := positiveNaturals_sound _ _ evidence.naturalExact
  have sizeNatural := exactNatural.1.trans dimensions
  rw [evidence.weights, propagateWeights_anchor vista witness.anchor natural sizeNatural]
  have hj : j.val < values.size := by omega
  have rational := (exactNatural.2 ⟨j.val, hj⟩).2
  simpa only [arrayVector, Array.getElem?_eq_getElem hj, Option.getD_some] using rational

theorem AuditExtracted.anchor_solution {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural) :
    NodeAnchorSolution vista witness.anchor leaders (fun i => (witness.weights[i]?.getD 0 : ℚ)) := by
  apply (anchorRows_satisfied_iff _ _ _ _).mp
  have coordinate : (fun j : Fin (levelNodes vista witness.anchor).length =>
      (witness.weights[(levelNodes vista witness.anchor)[j.val]]?.getD 0 : ℚ)) =
      arrayVector (levelNodes vista witness.anchor).length values := by
    funext j
    exact evidence.anchor_coordinate j
  rw [coordinate]
  exact (solveLinear_sound _ _ _ evidence.solved).2.2

theorem AuditExtracted.anchor_unique {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural)
    (z : Nat → ℚ) (solution : NodeAnchorSolution vista witness.anchor leaders z)
    (i : Nat) (present : i ∈ levelNodes vista witness.anchor) :
    z i = (witness.weights[i]?.getD 0 : ℚ) := by
  obtain ⟨j, equal⟩ := List.mem_iff_get.mp present
  have unique := solveLinear_unique _ _ _ evidence.solved
    (fun j => z (levelNodes vista witness.anchor)[j.val])
    ((anchorRows_satisfied_iff _ _ _ _).mpr solution)
  have same := congrFun unique j
  exact (congrArg z equal.symm).trans (same.trans (evidence.anchor_coordinate j).symm) |>.trans
    (congrArg (fun i => ((witness.weights[i]?.getD 0 : Nat) : ℚ)) equal)

theorem AuditExtracted.anchor_positive_weights {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural)
    (i : Nat) (present : i ∈ levelNodes vista witness.anchor) :
    0 < witness.weights[i]?.getD 0 := by
  obtain ⟨j, equal⟩ := List.mem_iff_get.mp present
  have dimensions := (solveLinear_sound _ _ _ evidence.solved).2.1
  have exactNatural := positiveNaturals_sound _ _ evidence.naturalExact
  have hj : j.val < values.size := by omega
  rw [← equal, evidence.weights]
  change 0 < (propagateWeights vista witness.anchor natural)[(levelNodes vista witness.anchor)[j.val]]?.getD 0
  rw [propagateWeights_anchor vista witness.anchor natural (exactNatural.1.trans dimensions) j]
  exact (exactNatural.2 ⟨j.val, hj⟩).1


theorem array_sum_coordinates (values : Array Nat) (n : Nat) (size : values.size = n) :
    (∑ j : Fin n, values[j.val]?.getD 0) = values.toList.sum := by
  subst n
  have list : List.ofFn (fun j : Fin values.size => values[j.val]?.getD 0) = values.toList := by
    have equal := congrArg Array.toList (Array.ofFn_getElem (xs := values))
    rw [Array.toList_ofFn] at equal
    refine Eq.trans ?_ equal
    apply congrArg List.ofFn
    funext j
    rw [Array.getElem?_eq_getElem j.isLt, Option.getD_some]
  rw [← List.sum_ofFn, list]

theorem AuditExtracted.anchor_total_weights {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural) :
    ((levelNodes vista witness.anchor).map (fun i => witness.weights[i]?.getD 0)).sum = candidate := by
  have size := (positiveNaturals_sound _ _ evidence.naturalExact).1.trans
    (solveLinear_sound _ _ _ evidence.solved).2.1
  rw [← sum_list_coordinates]
  calc
    _ = ∑ j : Fin (levelNodes vista witness.anchor).length, natural[j.val]?.getD 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [evidence.weights, propagateWeights_anchor vista witness.anchor natural size]
    _ = natural.toList.sum := array_sum_coordinates natural _ size
    _ = candidate := evidence.total

theorem list_sum_filter_map {M : Type*} [AddMonoid M] (nodes : List Nat) (p : Nat → Bool) (f : Nat → M) :
    ((nodes.filter p).map f).sum = (nodes.map (fun i => if p i then f i else 0)).sum := by
  induction nodes with
  | nil => rfl
  | cons i rest ih => cases hp : p i <;> simp [hp, ih]

theorem AuditExtracted.anchor_leader_weights {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural) :
    ((levelNodes vista witness.anchor).map (fun i =>
      if (vista.node i).leader then witness.weights[i]?.getD 0 else 0)).sum = leaders := by
  have equation := evidence.anchor_solution.2
  apply Nat.cast_injective (R := ℚ)
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def,
    apply_ite (fun n : Nat => (n : ℚ)), Nat.cast_zero] using equation

theorem AuditExtracted.anchor_flow {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural)
    (old : Nat) (present : old ∈ levelNodes vista (witness.anchor - 1)) :
    ((levelNodes vista witness.anchor).map (fun i =>
      countFrom (vista.node i) old * witness.weights[i]?.getD 0)).sum =
    ((children vista old witness.anchor).map (fun i =>
      (vista.node i).degree * witness.weights[i]?.getD 0)).sum := by
  rw [children, list_sum_filter_map]
  simp only [beq_iff_eq]
  have equation := evidence.anchor_solution.1 old present
  apply Nat.cast_injective (R := ℚ)
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_mul,
    apply_ite (fun n : Nat => (n : ℚ)), Nat.cast_zero] using equation

theorem AuditExtracted.all_flow {vista : Vista} {leaders candidate last : Nat}
    {witness : AuditWitness} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last witness values natural)
    (r : Nat) (below : r < witness.anchor) (old : Nat) (present : old ∈ levelNodes vista r) :
    ((levelNodes vista (r + 1)).map (fun i =>
      countFrom (vista.node i) old * witness.weights[i]?.getD 0)).sum =
    ((children vista old (r + 1)).map (fun i =>
      (vista.node i).degree * witness.weights[i]?.getD 0)).sum := by
  by_cases anchor : r + 1 = witness.anchor
  · have h := evidence.anchor_flow old (by simpa only [← anchor, Nat.add_sub_cancel] using present)
    simpa only [← anchor] using h
  · have within : r + 1 < witness.anchor := by omega
    have h := List.all_eq_true.mp evidence.flowCheck (r + 1) (List.mem_range.mpr within)
    have hz : (r + 1 == 0) = false := by simp
    rw [hz, Bool.false_or] at h
    exact beq_iff_eq.mp (List.all_eq_true.mp h old (by simpa only [Nat.add_sub_cancel] using present))

end Counting.Executable
