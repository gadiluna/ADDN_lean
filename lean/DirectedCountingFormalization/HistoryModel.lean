import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card

/-!
# Anonymous late-awareness histories as recursive equivalence relations

An attempted datatype with a constructor containing `Multiset History` is
rejected by Lean's strict-positivity checker.  This file uses the equivalent
and more economical presentation: two agents have the same history exactly
when their old histories, current outdegrees, and received multiplicities from
every old history class agree.

The round convention is the one used in the paper.  `G t u v` means that the
round-`t` communication graph contains the arc `u -> v`.  Thus the histories
at time `t + 1` use graph `G (t + 1)`.
-/

namespace DirectedCounting

/-- The number of outgoing neighbors of `v` in round `t`. -/
noncomputable def outdegree {V : Type*} (G : Nat → V → V → Prop)
    (t : Nat) (v : V) : Nat :=
  Set.ncard {w | G t v w}

/-- Recursive equality of anonymous late-awareness histories.

The last conjunct compares the multiplicity of every old history class in
the two received multisets.  Quantifying over representatives `w : V` merely
repeats the same equality for equivalent representatives and avoids choosing
a quotient enumeration. -/
noncomputable def sameHistory {V Input : Type*} (G : Nat → V → V → Prop)
    (input : V → Input) : Nat → V → V → Prop
  | 0, u, v => input u = input v
  | t + 1, u, v =>
      sameHistory G input t u v ∧
      outdegree G (t + 1) u = outdegree G (t + 1) v ∧
      ∀ w,
        Set.ncard {x | G (t + 1) x u ∧ sameHistory G input t x w} =
        Set.ncard {x | G (t + 1) x v ∧ sameHistory G input t x w}

@[simp] theorem sameHistory_zero {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (u v : V) :
    sameHistory G input 0 u v ↔ input u = input v :=
  Iff.rfl

@[simp] theorem sameHistory_succ {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat) (u v : V) :
    sameHistory G input (t + 1) u v ↔
      sameHistory G input t u v ∧
      outdegree G (t + 1) u = outdegree G (t + 1) v ∧
      ∀ w,
        Set.ncard {x | G (t + 1) x u ∧ sameHistory G input t x w} =
        Set.ncard {x | G (t + 1) x v ∧ sameHistory G input t x w} :=
  Iff.rfl

/-- Histories refine: equality after a new round implies equality before it. -/
theorem sameHistory_of_succ {V Input : Type*}
    {G : Nat → V → V → Prop} {input : V → Input} {t : Nat} {u v : V}
    (h : sameHistory G input (t + 1) u v) :
    sameHistory G input t u v :=
  h.1

theorem sameHistory_refl {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) :
    ∀ t v, sameHistory G input t v v := by
  intro t
  induction t with
  | zero => intro v; simp
  | succ t ih =>
      intro v
      exact ⟨ih v, rfl, fun _ ↦ rfl⟩

theorem sameHistory_symm {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) :
    ∀ t u v, sameHistory G input t u v → sameHistory G input t v u := by
  intro t
  induction t with
  | zero => intro u v h; exact h.symm
  | succ t ih =>
      intro u v h
      exact ⟨ih u v h.1, h.2.1.symm, fun w ↦ (h.2.2 w).symm⟩

theorem sameHistory_trans {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) :
    ∀ t u v w,
      sameHistory G input t u v →
      sameHistory G input t v w →
      sameHistory G input t u w := by
  intro t
  induction t with
  | zero => intro u v w huv hvw; exact huv.trans hvw
  | succ t ih =>
      intro u v w huv hvw
      exact ⟨ih u v w huv.1 hvw.1, huv.2.1.trans hvw.2.1,
        fun x ↦ (huv.2.2 x).trans (hvw.2.2 x)⟩

/-- The partition of agents into their history classes at time `t`. -/
noncomputable def historySetoid {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat) : Setoid V where
  r := sameHistory G input t
  iseqv :=
    ⟨sameHistory_refl G input t,
      fun h ↦ sameHistory_symm G input t _ _ h,
      fun h₁ h₂ ↦ sameHistory_trans G input t _ _ _ h₁ h₂⟩

/-- The type of global history classes at time `t`. -/
abbrev HistoryClass {V Input : Type*} (G : Nat → V → V → Prop)
    (input : V → Input) (t : Nat) :=
  Quotient (historySetoid G input t)

/-- Forgetting the newest round maps every new history class to its unique old
parent class. -/
noncomputable def forgetHistoryClass {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat) :
    HistoryClass G input (t + 1) → HistoryClass G input t :=
  Quotient.map id (fun _ _ h ↦ sameHistory_of_succ h)

/-- Every old class has at least one new child. -/
theorem forgetHistoryClass_surjective {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat) :
    Function.Surjective (forgetHistoryClass G input t) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  exact ⟨Quotient.mk'' v, rfl⟩

/-- A round branches when two agents equal before the round become different
after it. -/
def HistoryBranches {V Input : Type*} (G : Nat → V → V → Prop)
    (input : V → Input) (t : Nat) : Prop :=
  ∃ u v, sameHistory G input t u v ∧
    ¬sameHistory G input (t + 1) u v

/-- At a branching round, the parent map merges two distinct new classes. -/
theorem forgetHistoryClass_not_injective_of_branches {V Input : Type*}
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat)
    (hbranch : HistoryBranches G input t) :
    ¬Function.Injective (forgetHistoryClass G input t) := by
  rintro hinj
  obtain ⟨u, v, hold, hnew⟩ := hbranch
  have hparents :
      forgetHistoryClass G input t (Quotient.mk'' u) =
        forgetHistoryClass G input t (Quotient.mk'' v) :=
    Quotient.sound hold
  have hchildren := hinj hparents
  exact hnew (Quotient.exact hchildren)

/-- Consequently, on a finite network a branching round strictly increases
the number of history classes. -/
theorem historyClass_card_lt_of_branches {V Input : Type*} [Finite V]
    (G : Nat → V → V → Prop) (input : V → Input) (t : Nat)
    (hbranch : HistoryBranches G input t) :
    Nat.card (HistoryClass G input t) <
      Nat.card (HistoryClass G input (t + 1)) := by
  letI : Fintype (HistoryClass G input t) := Fintype.ofFinite _
  letI : Fintype (HistoryClass G input (t + 1)) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective
      (forgetHistoryClass G input t)
      (forgetHistoryClass_surjective G input t)
      (forgetHistoryClass_not_injective_of_branches G input t hbranch)

end DirectedCounting
