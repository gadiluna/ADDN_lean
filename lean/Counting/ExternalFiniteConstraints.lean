import Counting.ExternalEncoding

/-! Executable finite-domain constraint encoding into CNF. The size bound
depends exponentially only on the arity of each local constraint, not on
the total number of variables. This is the local encoding layer used by a
bounded computation tableau. -/
namespace Counting.External.FiniteConstraints

def tuples (d : ℕ) : (arity : ℕ) → List (Fin arity → Fin d)
  | 0 => [Fin.elim0]
  | arity + 1 => (List.finRange d).flatMap (fun head =>
      (tuples d arity).map (Fin.cons head))

theorem mem_tuples (d arity : ℕ) (tuple : Fin arity → Fin d) : tuple ∈ tuples d arity := by
  induction arity with
  | zero =>
      have same : tuple = Fin.elim0 := funext fun i => Fin.elim0 i
      simp [tuples, same]
  | succ arity ih =>
      rw [tuples, List.mem_flatMap]
      refine ⟨tuple 0, by simp, ?_⟩
      rw [List.mem_map]
      refine ⟨Fin.tail tuple, ih _, ?_⟩
      exact Fin.cons_self_tail tuple

theorem tuples_length (d arity : ℕ) : (tuples d arity).length = d ^ arity := by
  induction arity with
  | zero => simp [tuples]
  | succ arity ih => simp [tuples, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

structure Constraint (n d : ℕ) where
  arity : ℕ
  position : Fin arity → Fin n
  allowed : (Fin arity → Fin d) → Bool

def Constraint.Satisfied {n d : ℕ} (constraint : Constraint n d) (assignment : Fin n → Fin d) : Prop :=
  constraint.allowed (assignment ∘ constraint.position) = true

def bitIndex {n d : ℕ} (place : Fin n) (value : Fin d) : Fin (n*d) :=
  finProdFinEquiv (place, value)

def lit {n d : ℕ} (place : Fin n) (value : Fin d) (positive : Bool) : Literal (n*d) :=
  ⟨bitIndex place value, positive⟩

def encoding {n d : ℕ} (assignment : Fin n → Fin d) : Fin (n*d) → Bool :=
  fun index => decide (assignment (finProdFinEquiv.symm index).1 = (finProdFinEquiv.symm index).2)

@[simp] theorem encoding_variable {n d : ℕ} (assignment : Fin n → Fin d)
    (place : Fin n) (value : Fin d) :
    encoding assignment (bitIndex place value) = decide (assignment place = value) := by
  simp [encoding, bitIndex]

@[simp] theorem positive_eval {n d : ℕ} (assignment : Fin n → Fin d)
    (place : Fin n) (value : Fin d) :
    (lit place value true).eval (encoding assignment) = decide (assignment place = value) := by
  simp [lit, Literal.eval]

@[simp] theorem negative_eval {n d : ℕ} (assignment : Fin n → Fin d)
    (place : Fin n) (value : Fin d) :
    (lit place value false).eval (encoding assignment) = decide (assignment place ≠ value) := by
  simp [lit, Literal.eval]

def oneHot (n d : ℕ) : CNF (n*d) :=
  (List.finRange n).flatMap (fun place =>
    [(List.finRange d).map (fun value => lit place value true)] ++
      (List.finRange d).flatMap (fun first =>
        ((List.finRange d).filter (fun second => second ≠ first)).map
          (fun second => [lit place first false, lit place second false])))

def Constraint.toCNF {n d : ℕ} (constraint : Constraint n d) : CNF (n*d) :=
  ((tuples d constraint.arity).filter (fun tuple => !constraint.allowed tuple)).map
    (fun tuple => (List.finRange constraint.arity).map
      (fun position => lit (constraint.position position) (tuple position) false))

def toCNF {n d : ℕ} (constraints : List (Constraint n d)) : CNF (n*d) :=
  oneHot n d ++ constraints.flatMap Constraint.toCNF

theorem oneHot_eval_iff {n d : ℕ} (assignment : Fin (n*d) → Bool) :
    (oneHot n d).eval assignment = true ↔
      ∀ place, (∃ value, assignment (bitIndex place value) = true) ∧
        ∀ first second, first ≠ second →
          assignment (bitIndex place first) = false ∨ assignment (bitIndex place second) = false := by
  simp [oneHot, CNF.eval, List.all_flatMap, lit, Literal.eval, ne_comm, imp_iff_not_or]

theorem oneHot_encoding {n d : ℕ} (assignment : Fin n → Fin d) :
    (oneHot n d).eval (encoding assignment) = true := by
  rw [oneHot_eval_iff]
  intro place
  refine ⟨⟨assignment place, by simp⟩, ?_⟩
  intro first second different
  simp only [encoding_variable, decide_eq_false_iff_not]
  by_cases firstEq : assignment place = first
  · right
    intro secondEq
    exact different (firstEq.symm.trans secondEq)
  · exact Or.inl firstEq

theorem oneHot_exists_assignment {n d : ℕ} (assignment : Fin (n*d) → Bool)
    (accepted : (oneHot n d).eval assignment = true) :
    ∃ values : Fin n → Fin d, encoding values = assignment := by
  classical
  have conditions := (oneHot_eval_iff assignment).mp accepted
  choose values selected using fun place => (conditions place).1
  refine ⟨values, ?_⟩
  funext index
  obtain ⟨⟨place, value⟩, rfl⟩ := finProdFinEquiv.surjective index
  change encoding values (bitIndex place value) = assignment (bitIndex place value)
  rw [encoding_variable]
  by_cases same : values place = value
  · simp only [same, decide_true]
    exact (same ▸ selected place).symm
  · simp only [same, decide_false]
    have both := (conditions place).2 (values place) value same
    exact (both.resolve_left (by rw [selected place]; decide)).symm

theorem constraint_encoding_iff {n d : ℕ} (constraint : Constraint n d) (assignment : Fin n → Fin d) :
    constraint.toCNF.eval (encoding assignment) = true ↔ constraint.Satisfied assignment := by
  simp only [Constraint.toCNF, CNF.eval, List.all_map, List.all_eq_true, List.mem_filter,
    Bool.not_eq_true', and_imp, List.any_map, Function.comp_def, List.any_eq_true, List.mem_finRange,
    true_and, negative_eval, decide_eq_true_eq]
  constructor
  · intro accepted
    by_contra rejected
    have falseValue : constraint.allowed (assignment ∘ constraint.position) = false :=
      Bool.eq_false_iff.mpr rejected
    obtain ⟨position, impossible⟩ := accepted _ (mem_tuples _ _ _) falseValue
    exact impossible rfl
  · intro satisfied tuple member forbidden
    by_contra noDifference
    have same : assignment ∘ constraint.position = tuple := by
      funext position
      exact Classical.byContradiction fun different => noDifference ⟨position, different⟩
    rw [← same, satisfied] at forbidden
    contradiction

theorem encoding_iff {n d : ℕ} (constraints : List (Constraint n d)) (assignment : Fin n → Fin d) :
    (toCNF constraints).eval (encoding assignment) = true ↔
      ∀ constraint ∈ constraints, constraint.Satisfied assignment := by
  simp only [toCNF, CNF.eval, List.all_append, Bool.and_eq_true]
  change (oneHot n d).eval (encoding assignment) = true ∧ _ ↔ _
  simp only [oneHot_encoding, true_and]
  simp only [List.all_flatMap, List.all_eq_true]
  exact forall₂_congr fun constraint _ => by
    simpa only [CNF.eval, List.all_eq_true] using constraint_encoding_iff constraint assignment

theorem satisfiable_iff {n d : ℕ} (constraints : List (Constraint n d)) :
    (toCNF constraints).Satisfiable ↔
      ∃ assignment : Fin n → Fin d, ∀ constraint ∈ constraints, constraint.Satisfied assignment := by
  constructor
  · rintro ⟨assignment, accepted⟩
    have hot : (oneHot n d).eval assignment = true := by
      have := accepted
      simp only [toCNF, CNF.eval, List.all_append, Bool.and_eq_true] at this
      exact this.1
    obtain ⟨values, rfl⟩ := oneHot_exists_assignment assignment hot
    exact ⟨values, (encoding_iff constraints values).mp accepted⟩
  · rintro ⟨values, satisfied⟩
    exact ⟨encoding values, (encoding_iff constraints values).mpr satisfied⟩

end Counting.External.FiniteConstraints
