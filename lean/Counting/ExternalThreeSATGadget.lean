import Counting.ExternalCycle

namespace Counting.External.ThreeSAT

def slotCount (n m : ℕ) := n * (3 * m + 1)
abbrev Slot (n m : ℕ) := Fin n × Fin (3 * m + 1)
abbrev Extra (n m : ℕ) := Fin m ⊕ Fin (slotCount n m - m)
abbrev Place (n m : ℕ) := Slot n m ⊕ Extra n m
abbrev Port (n m : ℕ) := Bool × Slot n m

def occurrence {m : ℕ} (clause : Fin m) (position : Fin 3) : Fin (3 * m + 1) :=
  ⟨3 * clause.val + position.val, by have := clause.isLt; have := position.isLt; omega⟩

theorem occurrence_injective {m : ℕ} :
    Function.Injective (fun p : Fin m × Fin 3 => occurrence p.1 p.2) := by
  intro a b equal
  have values := congrArg Fin.val equal
  have := a.2.isLt
  have := b.2.isLt
  apply Prod.ext <;> apply Fin.ext
  · change 3 * a.1.val + a.2.val = 3 * b.1.val + b.2.val at values
    omega
  · change 3 * a.1.val + a.2.val = 3 * b.1.val + b.2.val at values
    omega

def literalSlot {n m : ℕ} (formula : ThreeSAT n m) (c : Fin m) (p : Fin 3) : Slot n m :=
  ((formula.literal c p).var, occurrence c p)

def literalPort {n m : ℕ} (formula : ThreeSAT n m) (c : Fin m) (p : Fin 3) : Port n m :=
  ((formula.literal c p).positive, formula.literalSlot c p)

def nextSlot {n m : ℕ} (v : Slot n m) : Slot n m :=
  (v.1, finRotate (3 * m + 1) v.2)

/-- Variable cycles, clause choices, and unrestricted completion slots.
Only clause positions use literal ports; all remaining slots complete the
matching without adding logical constraints. -/
def gadgetArc {n m : ℕ} (formula : ThreeSAT n m) :
    Place n m → Place n m → Port n m → Bool
  | .inl v, .inl w, z => decide (z.2 = v ∧
      ((z.1 = false ∧ w = v) ∨ (z.1 = true ∧ w = nextSlot v)))
  | .inr (.inl c), .inr (.inl d), z => decide (c = d ∧ ∃ p, z = formula.literalPort c p)
  | .inr (.inr g), .inr (.inr h), _ => decide (g = h)
  | _, _, _ => false

/-- Semantic perfect matching of the typed gadget. The explicit finite
edge-list representation is produced separately from this specification. -/
structure GadgetMatching {n m : ℕ} (formula : ThreeSAT n m) where
  partner : Equiv.Perm (Place n m)
  port : Place n m ≃ Port n m
  allowed : ∀ x, formula.gadgetArc x (partner x) (port x) = true

def GadgetMatching.choice {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (v : Slot n m) : Bool := !(M.port (.inl v)).1

theorem GadgetMatching.variable_data {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (v : Slot n m) :
    M.partner (.inl v) = .inl (if M.choice v then v else nextSlot v) ∧
      M.port (.inl v) = (!M.choice v, v) := by
  have allowed := M.allowed (.inl v)
  cases hp : M.partner (.inl v) with
  | inr extra => simp [gadgetArc, hp] at allowed
  | inl w =>
      have data : (M.port (.inl v)).2 = v ∧
          (((M.port (.inl v)).1 = false ∧ w = v) ∨
           ((M.port (.inl v)).1 = true ∧ w = nextSlot v)) := by
        simpa only [hp, gadgetArc, decide_eq_true_eq] using allowed
      rcases data.2 with ⟨off, rfl⟩ | ⟨on, rfl⟩
      · constructor
        · simp [choice, off]
        · apply Prod.ext <;> simp [choice, off, data.1]
      · constructor
        · simp [choice, on]
        · apply Prod.ext <;> simp [choice, on, data.1]

theorem GadgetMatching.choice_injective {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (i : Fin n) :
    Function.Injective (cycleChoice (finRotate (3 * m + 1)) (fun j => M.choice (i, j))) := by
  intro a b equal
  have partnerEq : M.partner (.inl (i, a)) = M.partner (.inl (i, b)) := by
    rw [(M.variable_data (i, a)).1, (M.variable_data (i, b)).1]
    apply congrArg Sum.inl
    have first : (if M.choice (i, a) then (i, a) else nextSlot (i, a)) =
        (i, cycleChoice (finRotate (3 * m + 1)) (fun j => M.choice (i, j)) a) := by
      unfold cycleChoice nextSlot
      split_ifs <;> rfl
    have second : (if M.choice (i, b) then (i, b) else nextSlot (i, b)) =
        (i, cycleChoice (finRotate (3 * m + 1)) (fun j => M.choice (i, j)) b) := by
      unfold cycleChoice nextSlot
      split_ifs <;> rfl
    rw [first, second, equal]
  exact congrArg Prod.snd (Sum.inl.inj (M.partner.injective partnerEq))

def GadgetMatching.assignment {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (i : Fin n) : Bool := M.choice (i, 0)

theorem GadgetMatching.choice_constant {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (v : Slot n m) : M.choice v = M.assignment v.1 :=
  cycleChoice_constant (3 * m) (fun j => M.choice (v.1, j)) (M.choice_injective v.1) v.2

theorem GadgetMatching.variable_port {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (v : Slot n m) :
    M.port (.inl v) = (!M.assignment v.1, v) := by
  rw [(M.variable_data v).2, M.choice_constant v]

theorem GadgetMatching.clause_port {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) (c : Fin m) :
    ∃ p, M.port (.inr (.inl c)) = formula.literalPort c p := by
  have allowed := M.allowed (.inr (.inl c))
  cases hp : M.partner (.inr (.inl c)) with
  | inl v => simp [gadgetArc, hp] at allowed
  | inr extra =>
      cases extra with
      | inr g => simp [gadgetArc, hp] at allowed
      | inl d =>
          exact (show c = d ∧ ∃ p, M.port (.inr (.inl c)) = formula.literalPort c p by
            simpa only [hp, gadgetArc, decide_eq_true_eq] using allowed).2

theorem GadgetMatching.satisfies {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) : formula.Satisfies M.assignment := by
  intro c
  obtain ⟨p, used⟩ := M.clause_port c
  refine ⟨p, ?_⟩
  have different : (!M.assignment (formula.literal c p).var) ≠ (formula.literal c p).positive := by
    intro equal
    have collision : M.port (.inl (formula.literalSlot c p)) = M.port (.inr (.inl c)) := by
      rw [M.variable_port, used]
      exact Prod.ext equal rfl
    have impossible := M.port.injective collision
    cases impossible
  unfold Literal.eval
  cases ha : M.assignment (formula.literal c p).var <;>
    cases hs : (formula.literal c p).positive <;> simp_all

theorem gadget_matching_implies_yes {n m : ℕ} {formula : ThreeSAT n m}
    (matching : Nonempty formula.GadgetMatching) : formula.Yes := by
  obtain ⟨M⟩ := matching
  exact ⟨M.assignment, M.satisfies⟩

theorem clauses_le_slots {n m : ℕ} (formula : ThreeSAT n m) : m ≤ slotCount n m := by
  by_cases zero : m = 0
  · omega
  · have positive := formula.variables_positive (Nat.pos_of_ne_zero zero)
    unfold slotCount
    nlinarith

end Counting.External.ThreeSAT
