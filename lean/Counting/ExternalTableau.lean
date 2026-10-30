import Counting.ExternalFiniteConstraintsSize

namespace Counting.External.Tableau
open FiniteConstraints

/-- A local evolution on a finite row. The two neighbor maps allow a ring
or an explicitly bounded tape; the concrete machine simulation chooses them. -/
structure Dynamics (width alphabet : ℕ) where
  left : Fin width → Fin width
  right : Fin width → Fin width
  rule : (Fin 3 → Fin alphabet) → Fin alphabet

abbrev Configuration (width alphabet : ℕ) := Fin width → Fin alphabet

def Dynamics.step {w d : ℕ} (dynamics : Dynamics w d) (config : Configuration w d) : Configuration w d :=
  fun place => dynamics.rule ![config (dynamics.left place), config place, config (dynamics.right place)]

def Dynamics.run {w d : ℕ} (dynamics : Dynamics w d) : ℕ → Configuration w d → Configuration w d
  | 0, config => config
  | time+1, config => dynamics.step (dynamics.run time config)

def index {T w : ℕ} (time : Fin (T+1)) (place : Fin w) : Fin ((T+1)*w) :=
  finProdFinEquiv (time, place)

def row {T w d : ℕ} (values : Fin ((T+1)*w) → Fin d) (time : Fin (T+1)) : Configuration w d :=
  fun place => values (index time place)

def initialConstraint {T w d : ℕ} (constraint : Constraint w d) : Constraint ((T+1)*w) d where
  arity := constraint.arity
  position := fun position => index 0 (constraint.position position)
  allowed := constraint.allowed

def transitionConstraint {T w d : ℕ} (dynamics : Dynamics w d) (time : Fin T) (place : Fin w) :
    Constraint ((T+1)*w) d where
  arity := 4
  position := ![index time.castSucc (dynamics.left place), index time.castSucc place,
    index time.castSucc (dynamics.right place), index time.succ place]
  allowed := fun tuple => decide (tuple 3 = dynamics.rule ![tuple 0, tuple 1, tuple 2])

def constraints {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d)) :
    List (Constraint ((T+1)*w) d) :=
  initial.map initialConstraint ++ (List.finRange T).flatMap (fun time =>
    (List.finRange w).map (transitionConstraint dynamics time))

def finalClause {T w d : ℕ} (accept : Fin d → Bool) : List (Literal (((T+1)*w)*d)) :=
  (List.finRange w).flatMap (fun place =>
    ((List.finRange d).filter accept).map (fun value => lit (index (Fin.last T) place) value true))

def formula {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (accept : Fin d → Bool) : CNF (((T+1)*w)*d) :=
  toCNF (constraints dynamics initial) ++ [finalClause accept]

theorem initialConstraint_iff {T w d : ℕ} (constraint : Constraint w d)
    (values : Fin ((T+1)*w) → Fin d) :
    (initialConstraint constraint).Satisfied values ↔ constraint.Satisfied (row values 0) := Iff.rfl

theorem transitionConstraint_iff {T w d : ℕ} (dynamics : Dynamics w d) (time : Fin T) (place : Fin w)
    (values : Fin ((T+1)*w) → Fin d) :
    (transitionConstraint dynamics time place).Satisfied values ↔
      row values time.succ place = dynamics.step (row values time.castSucc) place := by
  simp only [Constraint.Satisfied, transitionConstraint, Function.comp_def, decide_eq_true_eq]
  rfl

theorem constraints_iff {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (values : Fin ((T+1)*w) → Fin d) :
    (∀ constraint ∈ constraints dynamics initial, constraint.Satisfied values) ↔
      (∀ constraint ∈ initial, constraint.Satisfied (row values 0)) ∧
      ∀ time : Fin T, row values time.succ = dynamics.step (row values time.castSucc) := by
  simp only [constraints, List.forall_mem_append, List.forall_mem_map,
    initialConstraint_iff, List.forall_mem_flatMap, List.mem_finRange, forall_prop_of_true,
    transitionConstraint_iff, funext_iff]

theorem finalClause_iff {T w d : ℕ} (accept : Fin d → Bool) (values : Fin ((T+1)*w) → Fin d) :
    (finalClause accept).any (fun literal => literal.eval (encoding values)) = true ↔
      ∃ place, accept (row values (Fin.last T) place) = true := by
  simp only [finalClause, List.any_eq_true, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨literal, ⟨place, value, allowed, rfl⟩, positive⟩
    have equal : values (index (Fin.last T) place) = value := by
      simpa only [positive_eval, decide_eq_true_eq] using positive
    refine ⟨place, ?_⟩
    change accept (values (index (Fin.last T) place)) = true
    rw [equal]
    exact allowed
  · rintro ⟨place, allowed⟩
    refine ⟨lit (index (Fin.last T) place) (row values (Fin.last T) place) true,
      ⟨place, row values (Fin.last T) place, allowed, rfl⟩, ?_⟩
    simp only [positive_eval, row, decide_true]

theorem formula_encoding_iff {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (accept : Fin d → Bool) (values : Fin ((T+1)*w) → Fin d) :
    (formula dynamics initial accept).eval (encoding values) = true ↔
      ((∀ constraint ∈ initial, constraint.Satisfied (row values 0)) ∧
        ∀ time : Fin T, row values time.succ = dynamics.step (row values time.castSucc)) ∧
        ∃ place, accept (row values (Fin.last T) place) = true := by
  change ((toCNF (constraints dynamics initial)) ++ [finalClause accept]).eval (encoding values) = true ↔ _
  simp only [CNF.eval, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  change (toCNF (constraints dynamics initial)).eval (encoding values) = true ∧ _ ↔ _
  rw [encoding_iff, constraints_iff, finalClause_iff]

theorem trace_eq_run {T w d : ℕ} (dynamics : Dynamics w d) (trace : Fin (T+1) → Configuration w d)
    (transitions : ∀ time : Fin T, trace time.succ = dynamics.step (trace time.castSucc)) :
    ∀ time, trace time = dynamics.run time.val (trace 0) := by
  intro time
  induction time using Fin.induction with
  | zero => rfl
  | succ time ih =>
      rw [transitions, ih]
      rfl

def runValues {T w d : ℕ} (dynamics : Dynamics w d) (config : Configuration w d) :
    Fin ((T+1)*w) → Fin d := fun position =>
  dynamics.run (finProdFinEquiv.symm position).1.val config (finProdFinEquiv.symm position).2

@[simp] theorem row_runValues {T w d : ℕ} (dynamics : Dynamics w d) (config : Configuration w d)
    (time : Fin (T+1)) : row (runValues dynamics config) time = dynamics.run time.val config := by
  funext place
  simp [row, runValues, index]

/-- The tableau formula has a satisfying assignment precisely when one of
its permitted initial rows reaches an accepting symbol at the last row. -/
theorem satisfiable_iff {T w d : ℕ} (dynamics : Dynamics w d) (initial : List (Constraint w d))
    (accept : Fin d → Bool) :
    (formula (T := T) dynamics initial accept).Satisfiable ↔
      ∃ config : Configuration w d, (∀ constraint ∈ initial, constraint.Satisfied config) ∧
        ∃ place, accept (dynamics.run T config place) = true := by
  constructor
  · rintro ⟨assignment, accepted⟩
    have hot : (oneHot ((T+1)*w) d).eval assignment = true := by
      have h := accepted
      simp only [formula, toCNF, CNF.eval, List.all_append, Bool.and_eq_true] at h
      exact h.1.1
    obtain ⟨values, rfl⟩ := oneHot_exists_assignment assignment hot
    obtain ⟨⟨initialAccepted, transitions⟩, place, finalAccepted⟩ :=
      (formula_encoding_iff dynamics initial accept values).mp accepted
    have final := trace_eq_run dynamics (row values) transitions (Fin.last T)
    refine ⟨row values 0, initialAccepted, place, ?_⟩
    simpa only [final, Fin.val_last] using finalAccepted
  · rintro ⟨config, initialAccepted, place, finalAccepted⟩
    refine ⟨encoding (runValues (T := T) dynamics config), ?_⟩
    rw [formula_encoding_iff]
    simp only [row_runValues, Fin.val_zero, Dynamics.run, Fin.val_last]
    refine ⟨⟨initialAccepted, ?_⟩, place, finalAccepted⟩
    intro time
    rfl

end Counting.External.Tableau
