import DirectedCountingFormalization.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option warningAsError true

/-!
# Anonymous histories for dynamic multigraphs

A relational history model represents a round by a proposition `G t u v`,
which records whether an arc is present. The multiplicity model represents
each round by natural edge counts, including parallel arcs and self-loops.
The SIROCCO/JACM model additionally requires undirectedness. This module
provides recursive history equivalence for natural edge counts without
truncating parallel links.

`G t u v` is the number of messages sent from `u` to `v` in round `t`.
Undirectedness is the symmetry law `G t u v = G t v u`; self-loops need no
special case.  Histories compare the total multiplicity received from every
previous history class.  The explicit outdegree coordinate is redundant in
the undirected model but is retained so the definition also matches the
late-awareness directed convention used elsewhere in the project.
-/

namespace DirectedCounting

open scoped BigOperators

/-- Total outgoing message multiplicity of one agent in one round. -/
noncomputable def multigraphOutdegree {V : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (t : Nat) (v : V) : Nat :=
  ∑ w, G t v w

/-- Total multiplicity entering `target` from the equivalence class of
`representative` under `same`. -/
noncomputable def weightedIncomingFromClass {V : Type*} [Fintype V]
    (edge : V → V → Nat) (same : V → V → Prop)
    (target representative : V) : Nat := by
  classical
  exact ∑ source, if same source representative then edge source target else 0

/-- A weighted incoming class count is positive exactly when one member of
that class sends a positive-multiplicity message to the target. -/
theorem weightedIncomingFromClass_pos_iff
    {V : Type*} [Fintype V]
    (edge : V → V → Nat) (same : V → V → Prop)
    (target representative : V) :
    0 < weightedIncomingFromClass edge same target representative ↔
      ∃ source, same source representative ∧ 0 < edge source target := by
  classical
  unfold weightedIncomingFromClass
  rw [Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨source, hpositive⟩
    by_cases hsame : same source representative
    · exact ⟨source, hsame, by simpa [hsame] using hpositive⟩
    · simp [hsame] at hpositive
  · rintro ⟨source, hsame, hedge⟩
    exact ⟨source, by simpa [hsame] using hedge⟩

/-- Recursive equality of anonymous histories with natural-valued edge
multiplicities. -/
noncomputable def sameMultigraphHistory {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) : Nat → V → V → Prop
  | 0, u, v => input u = input v
  | t + 1, u, v =>
      sameMultigraphHistory G input t u v ∧
      multigraphOutdegree G (t + 1) u =
        multigraphOutdegree G (t + 1) v ∧
      ∀ representative,
        weightedIncomingFromClass (G (t + 1))
            (sameMultigraphHistory G input t) u representative =
          weightedIncomingFromClass (G (t + 1))
            (sameMultigraphHistory G input t) v representative

@[simp] theorem sameMultigraphHistory_zero
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) (u v : V) :
    sameMultigraphHistory G input 0 u v ↔ input u = input v :=
  Iff.rfl

@[simp] theorem sameMultigraphHistory_succ
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input)
    (t : Nat) (u v : V) :
    sameMultigraphHistory G input (t + 1) u v ↔
      sameMultigraphHistory G input t u v ∧
      multigraphOutdegree G (t + 1) u =
        multigraphOutdegree G (t + 1) v ∧
      ∀ representative,
        weightedIncomingFromClass (G (t + 1))
            (sameMultigraphHistory G input t) u representative =
          weightedIncomingFromClass (G (t + 1))
            (sameMultigraphHistory G input t) v representative :=
  Iff.rfl

/-- Histories refine after every multigraph round. -/
theorem sameMultigraphHistory_of_succ
    {V Input : Type*} [Fintype V]
    {G : Nat → V → V → Nat} {input : V → Input}
    {t : Nat} {u v : V}
    (h : sameMultigraphHistory G input (t + 1) u v) :
    sameMultigraphHistory G input t u v :=
  h.1

theorem sameMultigraphHistory_refl
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) :
    ∀ t v, sameMultigraphHistory G input t v v := by
  intro t
  induction t with
  | zero => intro v; simp
  | succ t ih =>
      intro v
      exact ⟨ih v, rfl, fun _ ↦ rfl⟩

theorem sameMultigraphHistory_symm
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) :
    ∀ t u v,
      sameMultigraphHistory G input t u v →
        sameMultigraphHistory G input t v u := by
  intro t
  induction t with
  | zero => intro u v h; exact h.symm
  | succ t ih =>
      intro u v h
      exact ⟨ih u v h.1, h.2.1.symm, fun w ↦ (h.2.2 w).symm⟩

theorem sameMultigraphHistory_trans
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) :
    ∀ t u v w,
      sameMultigraphHistory G input t u v →
      sameMultigraphHistory G input t v w →
        sameMultigraphHistory G input t u w := by
  intro t
  induction t with
  | zero => intro u v w huv hvw; exact huv.trans hvw
  | succ t ih =>
      intro u v w huv hvw
      exact ⟨ih u v w huv.1 hvw.1, huv.2.1.trans hvw.2.1,
        fun x ↦ (huv.2.2 x).trans (hvw.2.2 x)⟩

/-- History equivalence for one finite multigraph execution. -/
noncomputable def multigraphHistorySetoid
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) (t : Nat) : Setoid V where
  r := sameMultigraphHistory G input t
  iseqv :=
    ⟨sameMultigraphHistory_refl G input t,
      fun h ↦ sameMultigraphHistory_symm G input t _ _ h,
      fun h₁ h₂ ↦ sameMultigraphHistory_trans G input t _ _ _ h₁ h₂⟩

/-- Quotient of agents by their multigraph history at a fixed level. -/
abbrev MultigraphHistoryClass
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) (t : Nat) :=
  Quotient (multigraphHistorySetoid G input t)

/-- Forget the newest multigraph round. -/
noncomputable def forgetMultigraphHistoryClass
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) (t : Nat) :
    MultigraphHistoryClass G input (t + 1) →
      MultigraphHistoryClass G input t :=
  Quotient.map id (fun _ _ h ↦ sameMultigraphHistory_of_succ h)

/-- Every old multigraph history class has a child. -/
theorem forgetMultigraphHistoryClass_surjective
    {V Input : Type*} [Fintype V]
    (G : Nat → V → V → Nat) (input : V → Input) (t : Nat) :
    Function.Surjective (forgetMultigraphHistoryClass G input t) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  exact ⟨Quotient.mk'' v, rfl⟩

/-- A natural-valued dynamic graph is undirected when every round's
multiplicity matrix is symmetric. -/
def IsUndirectedMultigraph {V : Type*}
    (G : Nat → V → V → Nat) : Prop :=
  ∀ t u v, G t u v = G t v u

/-- Per-round connectivity ignores zero-multiplicity pairs. -/
def MultigraphRoundConnected {V : Type*}
    (G : Nat → V → V → Nat) (t : Nat) : Prop :=
  StronglyConnected (fun u v ↦ 0 < G t u v)

/-- Disjoint union of two multigraph executions. -/
def pairedMultigraph {V W : Type*}
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat) :
    Nat → Sum V W → Sum V W → Nat
  | t, Sum.inl u, Sum.inl v => G t u v
  | t, Sum.inr u, Sum.inr v => H t u v
  | _, _, _ => 0

/-- Disjoint union of two input assignments. -/
def pairedMultigraphInput {V W Input : Type*}
    (inputV : V → Input) (inputW : W → Input) : Sum V W → Input
  | Sum.inl v => inputV v
  | Sum.inr w => inputW w

/-- Equality of a reference and matching agent's multigraph histories. -/
noncomputable def crossSameMultigraphHistory
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input)
    (t : Nat) (v : V) (w : W) : Prop :=
  sameMultigraphHistory (pairedMultigraph G H)
    (pairedMultigraphInput inputV inputW) t (Sum.inl v) (Sum.inr w)

/-- Cross-execution multigraph history equality refines backwards. -/
theorem crossSameMultigraphHistory_of_succ
    {V W Input : Type*} [Fintype V] [Fintype W]
    {G : Nat → V → V → Nat} {H : Nat → W → W → Nat}
    {inputV : V → Input} {inputW : W → Input}
    {t : Nat} {v : V} {w : W}
    (h : crossSameMultigraphHistory G H inputV inputW (t + 1) v w) :
    crossSameMultigraphHistory G H inputV inputW t v w :=
  h.1

end DirectedCounting
