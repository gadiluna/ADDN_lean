import Counting.ExternalThreeDM

namespace Counting.External

/-- A signed variable from an explicit finite variable universe. `positive`
means the literal is satisfied when the variable is true. -/
structure Literal (n : ℕ) where
  var : Fin n
  positive : Bool
deriving DecidableEq, Repr

def Literal.eval {n : ℕ} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  assignment literal.var == literal.positive

def Literal.negate {n : ℕ} (literal : Literal n) : Literal n :=
  ⟨literal.var, !literal.positive⟩

@[simp] theorem Literal.eval_negate {n : ℕ} (literal : Literal n) (assignment : Fin n → Bool) :
    literal.negate.eval assignment = !(literal.eval assignment) := by
  rcases literal with ⟨v, positive⟩
  unfold negate eval
  cases positive <;> cases assignment v <;> rfl

/-- General CNF-SAT, including empty clauses and the empty conjunction. -/
abbrev CNF (n : ℕ) := List (List (Literal n))

def CNF.eval {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool) : Bool :=
  formula.all (fun clause => clause.any (fun literal => literal.eval assignment))

def CNF.Satisfiable {n : ℕ} (formula : CNF n) : Prop := ∃ assignment, formula.eval assignment = true

/-- Exactly three occurrences per clause. Literals may repeat and variables
may be unused; these cases require no preprocessing assumptions. -/
structure ThreeSAT (n m : ℕ) where
  literal : Fin m → Fin 3 → Literal n

def ThreeSAT.Satisfies {n m : ℕ} (formula : ThreeSAT n m) (assignment : Fin n → Bool) : Prop :=
  ∀ clause, ∃ position, (formula.literal clause position).eval assignment = true

instance {n m : ℕ} (formula : ThreeSAT n m) (assignment : Fin n → Bool) :
    Decidable (formula.Satisfies assignment) :=
  inferInstanceAs (Decidable (∀ clause, ∃ position, (formula.literal clause position).eval assignment = true))

def ThreeSAT.Yes {n m : ℕ} (formula : ThreeSAT n m) : Prop :=
  ∃ assignment, formula.Satisfies assignment

def ThreeSAT.toCNF {n m : ℕ} (formula : ThreeSAT n m) : CNF n :=
  (List.finRange m).map (fun clause => (List.finRange 3).map (formula.literal clause))

theorem ThreeSAT.toCNF_eval {n m : ℕ} (formula : ThreeSAT n m) (assignment : Fin n → Bool) :
    formula.toCNF.eval assignment = true ↔ formula.Satisfies assignment := by
  simp [CNF.eval, toCNF, Satisfies]

theorem ThreeSAT.toCNF_satisfiable {n m : ℕ} (formula : ThreeSAT n m) :
    formula.toCNF.Satisfiable ↔ formula.Yes :=
  exists_congr (formula.toCNF_eval ·)

theorem ThreeSAT.variables_positive {n m : ℕ} (formula : ThreeSAT n m) (clauses : 0 < m) : 0 < n :=
  (formula.literal ⟨0, clauses⟩ 0).var.pos

end Counting.External
