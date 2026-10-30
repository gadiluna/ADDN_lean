import Counting.ExternalTableau

namespace Counting.External.Tableau
open FiniteConstraints

theorem constraints_length {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d)) :
    (constraints (T := T) dynamics initial).length = initial.length + T*w := by
  simp [constraints, List.length_flatMap]

theorem constraints_arity {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (arity : ℕ) (initialBound : ∀ constraint ∈ initial, constraint.arity ≤ arity) :
    ∀ constraint ∈ constraints (T := T) dynamics initial, constraint.arity ≤ max arity 4 := by
  intro constraint member
  simp only [constraints, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨original, member, rfl⟩ | ⟨time, _, original, _, rfl⟩
  · exact (initialBound original member).trans (le_max_left _ _)
  · exact le_max_right _ _

theorem finalClause_length {T w d : ℕ} (accept : Fin d → Bool) :
    (finalClause (T := T) (w := w) accept).length ≤ w*d := by
  unfold finalClause
  apply (flatMap_length_le _ _ d ?_).trans (by simp)
  intro place _
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange

/-- Explicit bounds before binary encoding. The only exponent depending
on the local rule is the maximum constraint arity (four for transitions). -/
theorem size_bounds {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (accept : Fin d → Bool) (arity : ℕ) (positive : 0 < d)
    (initialBound : ∀ constraint ∈ initial, constraint.arity ≤ arity) :
    (formula (T := T) dynamics initial accept).length ≤
      ((T+1)*w) * (1+d*d) + (initial.length+T*w) * d^(max arity 4) + 1 ∧
    (formula (T := T) dynamics initial accept).width ≤
      ((T+1)*w) * (1+d*d) * (d+2) +
        (initial.length+T*w) * (d^(max arity 4) * max arity 4) + w*d := by
  have bounds := FiniteConstraints.size_bounds (constraints (T := T) dynamics initial)
    (max arity 4) positive (constraints_arity dynamics initial arity initialBound)
  rw [constraints_length] at bounds
  have finalBound := finalClause_length (T := T) (w := w) accept
  simp only [formula, List.length_append, List.length_singleton, width_append, CNF.width,
    Nat.add_zero]
  omega

end Counting.External.Tableau
