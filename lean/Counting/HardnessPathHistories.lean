import Counting.HardnessPathMessages

/-! Canonical path-prefix histories independent of physical group lengths.
After r rounds each group has singleton positions 0,...,r-1 and a common
suffix at positions at least r. -/

namespace Counting.HardnessPath

variable {I : Type} [Fintype I]

noncomputable def canonical (coeff : I → Nat) (C : Nat) :
    (r : Nat) → FullHistory r × (I → Nat → FullHistory r)
  | 0 => (true, fun _ _ => false)
  | r + 1 =>
    let old := canonical coeff C r
    ((old.1, C, ∑ i : I, ({old.2 i r} : Multiset (FullHistory r))),
      fun i p => (old.2 i p, 1, Multiset.replicate (coeff i) old.1 +
        match p with | 0 => 0 | q + 1 => {old.2 i q}))

noncomputable def leaderHistory (coeff : I → Nat) (C r : Nat) : FullHistory r := (canonical coeff C r).1
noncomputable def memberHistory (coeff : I → Nat) (C r : Nat) (i : I) (p : Nat) : FullHistory r :=
  (canonical coeff C r).2 i p

@[simp] theorem leaderHistory_zero (coeff : I → Nat) (C : Nat) : leaderHistory coeff C 0 = true := rfl
@[simp] theorem memberHistory_zero (coeff : I → Nat) (C : Nat) (i : I) (p : Nat) :
    memberHistory coeff C 0 i p = false := rfl

theorem leaderHistory_succ (coeff : I → Nat) (C r : Nat) :
    leaderHistory coeff C (r + 1) =
      (leaderHistory coeff C r, C, ∑ i : I, ({memberHistory coeff C r i r} : Multiset (FullHistory r))) := rfl

theorem memberHistory_succ (coeff : I → Nat) (C r : Nat) (i : I) (p : Nat) :
    memberHistory coeff C (r + 1) i p =
      (memberHistory coeff C r i p, 1, Multiset.replicate (coeff i) (leaderHistory coeff C r) +
        match p with | 0 => 0 | q + 1 => {memberHistory coeff C r i q}) := rfl

theorem member_ne_leader (coeff : I → Nat) (C r : Nat) (i : I) (p : Nat) :
    memberHistory coeff C r i p ≠ leaderHistory coeff C r := by
  induction r with
  | zero => simp
  | succ r ih =>
    intro same
    exact ih (congrArg Prod.fst same)

/-- The exact within-group partition: min(position,r) is its class. -/
theorem member_eq_iff_min (coeff : I → Nat) (C r : Nat) (i : I) (p q : Nat) :
    memberHistory coeff C r i p = memberHistory coeff C r i q ↔ min p r = min q r := by
  induction r generalizing p q with
  | zero => simp
  | succ r ih =>
    let msg (p : Nat) : Multiset (FullHistory r) :=
      match p with | 0 => 0 | q + 1 => {memberHistory coeff C r i q}
    have step : memberHistory coeff C (r + 1) i p = memberHistory coeff C (r + 1) i q ↔
        memberHistory coeff C r i p = memberHistory coeff C r i q ∧ msg p = msg q := by
      constructor
      · intro same
        refine ⟨congrArg Prod.fst same, ?_⟩
        have hm := congrArg (fun h : FullHistory (r + 1) => h.2.2) same
        exact add_left_cancel hm
      · rintro ⟨prev, messages⟩
        change (memberHistory coeff C r i p, (1, _)) = (memberHistory coeff C r i q, (1, _))
        apply Prod.ext prev
        refine Prod.ext rfl ?_
        exact congrArg (fun m => Multiset.replicate (coeff i) (leaderHistory coeff C r) + m) messages
    rw [step, ih]
    cases p with
    | zero =>
      cases q with
      | zero => simp
      | succ q =>
        simp only [msg, Multiset.zero_ne_singleton, and_false, Nat.zero_min]
        constructor
        · exact False.elim
        · intro eq
          exact (ne_of_gt (lt_min (Nat.succ_pos q) (Nat.succ_pos r))) eq.symm
    | succ p =>
      cases q with
      | zero =>
        simp only [msg, Multiset.singleton_ne_zero, and_false, Nat.zero_min]
        constructor
        · exact False.elim
        · intro eq
          exact (ne_of_gt (lt_min (Nat.succ_pos p) (Nat.succ_pos r))) eq
      | succ q =>
        simp only [msg, Multiset.singleton_inj, ih]
        omega

theorem member_suffix (coeff : I → Nat) (C r : Nat) (i : I) (p : Nat) (suffix : r ≤ p) :
    memberHistory coeff C r i p = memberHistory coeff C r i r :=
  (member_eq_iff_min coeff C r i p r).mpr (by omega)

/-- Distinct coefficients are distinguished already by first-round
receipts of the initial leader state. -/
private def firstMessages (c p : Nat) : Multiset Bool :=
  Multiset.replicate c true + match p with | 0 => 0 | _ + 1 => {false}

private theorem firstMessages_eq (coeff : I → Nat) (C : Nat) (i : I) (p : Nat) :
    (memberHistory coeff C 1 i p).2.2 = firstMessages (coeff i) p := by
  cases p <;> rfl

theorem coefficient_eq_of_member_eq (coeff : I → Nat) (C r : Nat) (positive : 0 < r)
    (i j : I) (p q : Nat)
    (same : memberHistory coeff C r i p = memberHistory coeff C r j q) : coeff i = coeff j := by
  classical
  induction r with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      have messages := congrArg (fun h : FullHistory 1 => h.2.2) same
      rw [firstMessages_eq, firstMessages_eq] at messages
      have receipts := congrArg (fun s : Multiset Bool => s.count true) messages
      cases p <;> cases q <;> simpa [firstMessages] using receipts
    | succ r => exact ih (by omega) (congrArg Prod.fst same)

theorem member_partition (coeff : I → Nat) (distinct : Function.Injective coeff) (C r : Nat)
    (positive : 0 < r) (i j : I) (p q : Nat) :
    memberHistory coeff C r i p = memberHistory coeff C r j q ↔ i = j ∧ min p r = min q r := by
  constructor
  · intro same
    have groups := distinct (coefficient_eq_of_member_eq coeff C r positive i j p q same)
    subst j
    exact ⟨rfl, (member_eq_iff_min coeff C r i p q).mp same⟩
  · rintro ⟨rfl, pos⟩
    exact (member_eq_iff_min coeff C r i p q).mpr pos

end Counting.HardnessPath
