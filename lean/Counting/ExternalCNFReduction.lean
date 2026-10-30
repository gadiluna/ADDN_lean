import Counting.ExternalCNFGates

namespace Counting.External.CNF

def width {n : ℕ} : CNF n → ℕ
  | [] => 0
  | clause :: rest => clause.length + width rest

theorem member_length_le_width {n : ℕ} (formula : CNF n) (clause : List (Literal n))
    (member : clause ∈ formula) : clause.length ≤ formula.width := by
  induction formula with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp [width]
      · have bound := ih later
        simp only [width]
        omega

def clause {n : ℕ} (formula : CNF n) (c : Fin formula.length) : List (Literal n) := formula[c.val]

theorem clause_length_le_width {n : ℕ} (formula : CNF n) (c : Fin formula.length) :
    (formula.clause c).length ≤ formula.width :=
  formula.member_length_le_width _ (List.getElem_mem _)

def targetVariables {n : ℕ} (formula : CNF n) := n + formula.length * (formula.width + 1)
def targetClauses {n : ℕ} (formula : CNF n) := formula.length * (3 * formula.width + 2)

def variableEquiv {n : ℕ} (formula : CNF n) :
    Fin n ⊕ (Fin formula.length × Fin (formula.width + 1)) ≃ Fin formula.targetVariables :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def liftLiteral {n : ℕ} (formula : CNF n) (literal : Literal n) : Literal formula.targetVariables :=
  ⟨formula.variableEquiv (.inl literal.var), literal.positive⟩

def freshLiteral {n : ℕ} (formula : CNF n) (c : Fin formula.length) (j : Fin (formula.width + 1)) :
    Literal formula.targetVariables := ⟨formula.variableEquiv (.inr (c, j)), true⟩

/-- Positions beyond a short clause use its false terminal variable. -/
def atomLiteral {n : ℕ} (formula : CNF n) (c : Fin formula.length) (j : Fin formula.width) :
    Literal formula.targetVariables :=
  match (formula.clause c)[j.val]? with
  | some literal => formula.liftLiteral literal
  | none => formula.freshLiteral c (Fin.last formula.width)

abbrev Row {n : ℕ} (formula : CNF n) := (Fin formula.width × Fin 3) ⊕ Fin 2

def rowEquiv {n : ℕ} (formula : CNF n) : Row formula ≃ Fin (3 * formula.width + 2) :=
  (Equiv.sumCongr (finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _))) (Equiv.refl _)).trans finSumFinEquiv

def clauseEquiv {n : ℕ} (formula : CNF n) :
    Fin formula.length × Row formula ≃ Fin formula.targetClauses :=
  (Equiv.prodCongr (Equiv.refl _) formula.rowEquiv).trans finProdFinEquiv

def rowLiteral {n : ℕ} (formula : CNF n) (c : Fin formula.length) : Row formula → Fin 3 → Literal formula.targetVariables
  | .inl (j, row) => orRows (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j)
      (formula.freshLiteral c j.succ) row
  | .inr terminal => fun _ => if terminal = 0 then formula.freshLiteral c 0
      else (formula.freshLiteral c (Fin.last formula.width)).negate

def toThreeSAT {n : ℕ} (formula : CNF n) : ThreeSAT formula.targetVariables formula.targetClauses where
  literal index := formula.rowLiteral (formula.clauseEquiv.symm index).1 (formula.clauseEquiv.symm index).2

@[simp] theorem toThreeSAT_literal {n : ℕ} (formula : CNF n) (c : Fin formula.length)
    (row : Row formula) (p : Fin 3) :
    formula.toThreeSAT.literal (formula.clauseEquiv (c, row)) p = formula.rowLiteral c row p := by
  simp only [toThreeSAT, Equiv.symm_apply_apply]

def freshValue {n : ℕ} (formula : CNF n) (assignment : Fin formula.targetVariables → Bool)
    (c : Fin formula.length) (j : Fin (formula.width + 1)) : Bool :=
  assignment (formula.variableEquiv (.inr (c, j)))

@[simp] theorem freshLiteral_eval {n : ℕ} (formula : CNF n) (assignment : Fin formula.targetVariables → Bool)
    (c : Fin formula.length) (j : Fin (formula.width + 1)) :
    (formula.freshLiteral c j).eval assignment = formula.freshValue assignment c j := by
  simp [freshLiteral, freshValue, Literal.eval]

theorem toThreeSAT_satisfies_iff {n : ℕ} (formula : CNF n)
    (assignment : Fin formula.targetVariables → Bool) :
    formula.toThreeSAT.Satisfies assignment ↔
      ∀ c, formula.freshValue assignment c 0 = true ∧
        formula.freshValue assignment c (Fin.last formula.width) = false ∧
        ∀ j : Fin formula.width, formula.freshValue assignment c j.castSucc =
          ((formula.atomLiteral c j).eval assignment || formula.freshValue assignment c j.succ) := by
  constructor
  · intro satisfies c
    have root := satisfies (formula.clauseEquiv (c, .inr 0))
    have tail := satisfies (formula.clauseEquiv (c, .inr 1))
    simp only [toThreeSAT_literal, rowLiteral, reduceIte, freshLiteral_eval] at root tail
    refine ⟨root.choose_spec, by simpa using tail.choose_spec, ?_⟩
    intro j
    have rows : ∀ row, ∃ p, (orRows (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j)
        (formula.freshLiteral c j.succ) row p).eval assignment = true := by
      intro row
      simpa only [toThreeSAT_literal, rowLiteral] using satisfies (formula.clauseEquiv (c, .inl (j, row)))
    simpa only [freshLiteral_eval] using (orRows_satisfied _ _ _ assignment).mp rows
  · intro checks index
    obtain ⟨⟨c, row⟩, rfl⟩ := formula.clauseEquiv.surjective index
    simp only [toThreeSAT_literal]
    cases row with
    | inl data =>
        rcases data with ⟨j, row⟩
        have rows := (orRows_satisfied (formula.freshLiteral c j.castSucc) (formula.atomLiteral c j)
          (formula.freshLiteral c j.succ) assignment).mpr (by
            simpa only [freshLiteral_eval] using (checks c).2.2 j)
        exact rows row
    | inr terminal =>
        fin_cases terminal
        · exact ⟨0, by simpa [rowLiteral] using (checks c).1⟩
        · exact ⟨0, by simp [rowLiteral, (checks c).2.1]⟩

end Counting.External.CNF
