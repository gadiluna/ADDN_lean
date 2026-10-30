import Counting.ExternalSAT

namespace Counting.External

def tripleLiterals {n : ℕ} (a b c : Literal n) (p : Fin 3) : Literal n :=
  if p = 0 then a else if p = 1 then b else c

theorem tripleLiterals_satisfied {n : ℕ} (a b c : Literal n) (assignment : Fin n → Bool) :
    (∃ p, (tripleLiterals a b c p).eval assignment = true) ↔
      a.eval assignment = true ∨ b.eval assignment = true ∨ c.eval assignment = true := by
  constructor
  · rintro ⟨p, satisfied⟩
    fin_cases p <;> simp_all [tripleLiterals]
  · rintro (h | h | h)
    · exact ⟨0, by simpa [tripleLiterals] using h⟩
    · exact ⟨1, by simpa [tripleLiterals] using h⟩
    · exact ⟨2, by simpa [tripleLiterals] using h⟩

/-- Three clauses encode output ↔ (left ∨ right). Repeated literals pad
the two-literal clauses without changing their truth values. -/
def orRows {n : ℕ} (output left right : Literal n) (row : Fin 3) : Fin 3 → Literal n :=
  if row = 0 then tripleLiterals output.negate left right
  else if row = 1 then tripleLiterals output left.negate left.negate
  else tripleLiterals output right.negate right.negate

theorem orRows_satisfied {n : ℕ} (output left right : Literal n) (assignment : Fin n → Bool) :
    (∀ row, ∃ p, (orRows output left right row p).eval assignment = true) ↔
      output.eval assignment = (left.eval assignment || right.eval assignment) := by
  have rows : (∀ row, ∃ p, (orRows output left right row p).eval assignment = true) ↔
      ((output.negate.eval assignment = true ∨ left.eval assignment = true ∨ right.eval assignment = true) ∧
       (output.eval assignment = true ∨ left.negate.eval assignment = true) ∧
       (output.eval assignment = true ∨ right.negate.eval assignment = true)) := by
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      simp [orRows, tripleLiterals_satisfied] at h0 h1 h2
      exact ⟨by simpa using h0, by simpa using h1, by simpa using h2⟩
    · rintro ⟨h0, h1, h2⟩ row
      fin_cases row <;> simp_all [orRows, tripleLiterals_satisfied]
  rw [rows]
  simp only [Literal.eval_negate]
  cases output.eval assignment <;> cases left.eval assignment <;> cases right.eval assignment <;> decide

theorem list_suffix_step {A : Type*} (values : List A) (test : A → Bool) (j : ℕ) :
    (values.drop j).any test = ((values[j]?.map test).getD false || (values.drop (j + 1)).any test) := by
  induction j generalizing values with
  | zero => cases values <;> rfl
  | succ j ih =>
      cases values with
      | nil => rfl
      | cons a rest => simpa only [List.drop_succ_cons, List.getElem?_cons_succ] using ih rest

end Counting.External
