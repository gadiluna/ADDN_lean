import Counting.ExternalFiniteConstraints

namespace Counting.External.FiniteConstraints

theorem flatMap_length_le {A B : Type} (values : List A) (output : A → List B) (bound : ℕ)
    (bounded : ∀ value ∈ values, (output value).length ≤ bound) :
    (values.flatMap output).length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have first := bounded value List.mem_cons_self
      have tail := ih (fun other member => bounded other (List.mem_cons_of_mem value member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

theorem width_append {n : ℕ} (first second : CNF n) :
    (first ++ second).width = first.width + second.width := by
  induction first with
  | nil => simp [CNF.width]
  | cons clause rest ih => simp [CNF.width, ih, Nat.add_assoc]

theorem width_le_length_mul {n : ℕ} (formula : CNF n) (bound : ℕ)
    (bounded : ∀ clause ∈ formula, clause.length ≤ bound) :
    formula.width ≤ formula.length * bound := by
  induction formula with
  | nil => simp [CNF.width]
  | cons clause rest ih =>
      have first := bounded clause List.mem_cons_self
      have tail := ih (fun other member => bounded other (List.mem_cons_of_mem clause member))
      simp only [CNF.width, List.length_cons]
      nlinarith

theorem flatMap_width_le {A : Type} {n : ℕ} (values : List A) (output : A → CNF n) (bound : ℕ)
    (bounded : ∀ value ∈ values, (output value).width ≤ bound) :
    CNF.width (values.flatMap output) ≤ values.length * bound := by
  induction values with
  | nil => simp [CNF.width]
  | cons value rest ih =>
      have first := bounded value List.mem_cons_self
      have tail := ih (fun other member => bounded other (List.mem_cons_of_mem value member))
      simp only [List.flatMap_cons, width_append, List.length_cons]
      nlinarith

theorem oneHot_length (n d : ℕ) : (oneHot n d).length ≤ n * (1+d*d) := by
  unfold oneHot
  apply (flatMap_length_le _ _ (1+d*d) ?_).trans (by simp)
  intro place _
  have pairs := flatMap_length_le (List.finRange d)
    (fun first => ((List.finRange d).filter (fun second => second ≠ first)).map
      (fun second => [lit place first false, lit place second false])) d (by
        intro first _
        simpa only [List.length_map, List.length_finRange] using
          (List.length_filter_le (fun second : Fin d => second ≠ first) (List.finRange d)))
  simp only [List.length_finRange] at pairs
  simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_left pairs 1

theorem oneHot_clause_length {n d : ℕ} (clause : List (Literal (n*d)))
    (member : clause ∈ oneHot n d) : clause.length ≤ d+2 := by
  simp only [oneHot, List.mem_flatMap, List.mem_append, List.mem_singleton, List.mem_map] at member
  obtain ⟨place, _, first | ⟨a, _, b, _, second⟩⟩ := member
  · subst clause
    simp
  · subst clause
    simp

theorem oneHot_width (n d : ℕ) : (oneHot n d).width ≤ n * (1+d*d) * (d+2) := by
  exact (width_le_length_mul _ _ (fun clause member => oneHot_clause_length clause member)).trans
    (Nat.mul_le_mul_right (d+2) (oneHot_length n d))

theorem constraint_length {n d : ℕ} (constraint : Constraint n d) :
    constraint.toCNF.length ≤ d ^ constraint.arity := by
  simp only [Constraint.toCNF, List.length_map]
  exact (List.length_filter_le _ _).trans_eq (tuples_length _ _)

theorem constraint_clause_length {n d : ℕ} (constraint : Constraint n d)
    (clause : List (Literal (n*d))) (member : clause ∈ constraint.toCNF) :
    clause.length = constraint.arity := by
  obtain ⟨tuple, _, rfl⟩ := List.mem_map.mp member
  simp

theorem constraint_width {n d : ℕ} (constraint : Constraint n d) :
    constraint.toCNF.width ≤ d ^ constraint.arity * constraint.arity := by
  exact (width_le_length_mul _ _ (fun clause member =>
    (constraint_clause_length constraint clause member).le)).trans
      (Nat.mul_le_mul_right constraint.arity (constraint_length constraint))

/-- With bounded local arity, all combinatorial sizes are polynomial in
the number of positions and constraints. The alphabet size is kept explicit. -/
theorem size_bounds {n d : ℕ} (constraints : List (Constraint n d)) (arity : ℕ)
    (positive : 0 < d) (bounded : ∀ constraint ∈ constraints, constraint.arity ≤ arity) :
    (toCNF constraints).length ≤ n * (1+d*d) + constraints.length * d^arity ∧
      (toCNF constraints).width ≤ n * (1+d*d) * (d+2) + constraints.length * (d^arity*arity) := by
  have lengths := flatMap_length_le constraints Constraint.toCNF (d^arity) (by
    intro constraint member
    exact (constraint_length constraint).trans (Nat.pow_le_pow_right positive (bounded constraint member)))
  have widths := flatMap_width_le constraints Constraint.toCNF (d^arity*arity) (by
    intro constraint member
    exact (constraint_width constraint).trans (Nat.mul_le_mul
      (Nat.pow_le_pow_right positive (bounded constraint member)) (bounded constraint member)))
  have hotLength := oneHot_length n d
  have hotWidth := oneHot_width n d
  simp only [toCNF, List.length_append, width_append]
  omega

end Counting.External.FiniteConstraints
