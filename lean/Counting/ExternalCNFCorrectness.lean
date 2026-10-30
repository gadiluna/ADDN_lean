import Counting.ExternalCNFReduction

namespace Counting.External.CNF

def restrictAssignment {n : ℕ} (formula : CNF n) (assignment : Fin formula.targetVariables → Bool) :
    Fin n → Bool := fun v => assignment (formula.variableEquiv (.inl v))

def suffix {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool)
    (c : Fin formula.length) (j : ℕ) : Bool :=
  ((formula.clause c).drop j).any (fun literal => literal.eval assignment)

theorem suffix_last {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool) (c : Fin formula.length) :
    formula.suffix assignment c formula.width = false := by
  unfold suffix
  rw [List.drop_eq_nil_iff.mpr (formula.clause_length_le_width c)]
  rfl

theorem atomLiteral_eval {n : ℕ} (formula : CNF n) (assignment : Fin formula.targetVariables → Bool)
    (c : Fin formula.length) (j : Fin formula.width)
    (tail : formula.freshValue assignment c (Fin.last formula.width) = false) :
    (formula.atomLiteral c j).eval assignment =
      (((formula.clause c)[j.val]?).map (fun literal => literal.eval (formula.restrictAssignment assignment))).getD false := by
  unfold atomLiteral
  cases h : (formula.clause c)[j.val]? with
  | none => simpa only [freshLiteral_eval, Option.map_none, Option.getD_none] using tail
  | some literal => rfl

theorem eval_iff_clauses {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool) :
    formula.eval assignment = true ↔
      ∀ c : Fin formula.length, (formula.clause c).any (fun literal => literal.eval assignment) = true := by
  simp only [eval, List.all_eq_true]
  constructor
  · intro all c
    exact all _ (List.getElem_mem _)
  · intro all c member
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
    exact all ⟨i, hi⟩

theorem toThreeSAT_sound_assignment {n : ℕ} (formula : CNF n)
    (assignment : Fin formula.targetVariables → Bool)
    (satisfies : formula.toThreeSAT.Satisfies assignment) :
    formula.eval (formula.restrictAssignment assignment) = true := by
  have checks := (formula.toThreeSAT_satisfies_iff assignment).mp satisfies
  apply (formula.eval_iff_clauses _).mpr
  intro c
  have suffixValues : ∀ j : Fin (formula.width + 1),
      formula.freshValue assignment c j = formula.suffix (formula.restrictAssignment assignment) c j.val := by
    intro j
    induction j using Fin.reverseInduction with
    | last => simpa only [Fin.val_last, formula.suffix_last] using (checks c).2.1
    | cast j ih =>
        rw [(checks c).2.2 j, ih, formula.atomLiteral_eval assignment c j (checks c).2.1]
        exact (list_suffix_step (formula.clause c)
          (fun literal => literal.eval (formula.restrictAssignment assignment)) j.val).symm
  have root := suffixValues 0
  rw [(checks c).1] at root
  exact root.symm

def extendAssignment {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool) :
    Fin formula.targetVariables → Bool := fun v =>
  match formula.variableEquiv.symm v with
  | .inl original => assignment original
  | .inr (c, j) => formula.suffix assignment c j.val

@[simp] theorem restrict_extend {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool) :
    formula.restrictAssignment (formula.extendAssignment assignment) = assignment := by
  funext v
  simp [restrictAssignment, extendAssignment]

@[simp] theorem fresh_extend {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool)
    (c : Fin formula.length) (j : Fin (formula.width + 1)) :
    formula.freshValue (formula.extendAssignment assignment) c j = formula.suffix assignment c j.val := by
  simp [freshValue, extendAssignment]

theorem toThreeSAT_complete_assignment {n : ℕ} (formula : CNF n) (assignment : Fin n → Bool)
    (satisfies : formula.eval assignment = true) :
    formula.toThreeSAT.Satisfies (formula.extendAssignment assignment) := by
  apply (formula.toThreeSAT_satisfies_iff _).mpr
  intro c
  have tail : formula.freshValue (formula.extendAssignment assignment) c (Fin.last formula.width) = false := by
    rw [fresh_extend, Fin.val_last, suffix_last]
  refine ⟨?_, tail, ?_⟩
  · rw [fresh_extend]
    exact (formula.eval_iff_clauses assignment).mp satisfies c
  · intro j
    rw [fresh_extend, fresh_extend, formula.atomLiteral_eval _ c j tail, restrict_extend]
    exact list_suffix_step (formula.clause c) (fun literal => literal.eval assignment) j.val

theorem toThreeSAT_yes_iff {n : ℕ} (formula : CNF n) :
    formula.toThreeSAT.Yes ↔ formula.Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨formula.restrictAssignment assignment, formula.toThreeSAT_sound_assignment assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨formula.extendAssignment assignment, formula.toThreeSAT_complete_assignment assignment satisfies⟩

/-- Size bounds in an explicit input measure dominating variables,
clauses and literal occurrences. Runtime on the fixed machine is separate. -/
theorem toThreeSAT_size_polynomial {n : ℕ} (formula : CNF n) (L : ℕ)
    (varBound : n ≤ L) (clauses : formula.length ≤ L) (occurrences : formula.width ≤ L) :
    formula.targetVariables ≤ L + L * (L + 1) ∧ formula.targetClauses ≤ L * (3 * L + 2) := by
  constructor
  · have product := Nat.mul_le_mul clauses (show formula.width + 1 ≤ L + 1 by omega)
    unfold targetVariables
    omega
  · exact Nat.mul_le_mul clauses (by omega)

end Counting.External.CNF
