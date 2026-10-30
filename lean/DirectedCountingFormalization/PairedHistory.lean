import DirectedCountingFormalization.Flooding
import DirectedCountingFormalization.HistoryModel
import Mathlib.Tactic

set_option warningAsError true

/-!
# Histories shared by two executions

This module starts closing the semantic gap in the proposed linear counting
argument.  Two executions are placed side by side in a disjoint-union
execution.  Equality of histories in that union is then literal recursive
history equality, rather than an informal comparison of two view diagrams.

The main result, `exists_cross_match_of_equal_leaders`, is the positivity
bridge needed by the cross-execution potential.  If the two leaders have the
same history through time `T`, then every history class of the reference
execution at least `|V|-1` rounds before `T` has a representative in the other
execution.  The proof combines directed dynamic flooding with exact transport
of received-message multiplicities.
-/

namespace DirectedCounting

/-- Disjoint union of two dynamic executions.  There are no communication
arcs between the two components. -/
def pairedGraph {V W : Type*}
    (G : ℕ → V → V → Prop) (H : ℕ → W → W → Prop) :
    ℕ → Sum V W → Sum V W → Prop
  | t, Sum.inl u, Sum.inl v => G t u v
  | t, Sum.inr u, Sum.inr v => H t u v
  | _, _, _ => False

/-- Common input alphabet on the disjoint union. -/
def pairedInput {V W Input : Type*}
    (inputV : V → Input) (inputW : W → Input) : Sum V W → Input
  | Sum.inl v => inputV v
  | Sum.inr w => inputW w

/-- A reference agent and a matching agent have the same recursive history
through time `t`. -/
noncomputable def crossSameHistory {V W Input : Type*}
    (G : ℕ → V → V → Prop) (H : ℕ → W → W → Prop)
    (inputV : V → Input) (inputW : W → Input)
    (t : ℕ) (v : V) (w : W) : Prop :=
  sameHistory (pairedGraph G H) (pairedInput inputV inputW) t
    (Sum.inl v) (Sum.inr w)

/-- Outdegree in the left component of the paired execution is the original
left-execution outdegree. -/
theorem outdegree_pairedGraph_inl
    {V W : Type*} [Fintype V] [Fintype W]
    (G : ℕ → V → V → Prop) (H : ℕ → W → W → Prop)
    (t : ℕ) (v : V) :
    outdegree (pairedGraph G H) t (Sum.inl v) = outdegree G t v := by
  classical
  unfold outdegree
  symm
  apply Set.ncard_congr
    (s := {w : V | G t v w})
    (t := {a : Sum V W | pairedGraph G H t (Sum.inl v) a})
    (fun w _ ↦ Sum.inl w)
  · intro w hw
    simpa [pairedGraph] using hw
  · intro a b ha hb hab
    exact Sum.inl_injective hab
  · intro a ha
    cases a with
    | inl w => exact ⟨w, by simpa [pairedGraph] using ha, rfl⟩
    | inr w => simp [pairedGraph] at ha

/-- The analogous outdegree identity for the right component. -/
theorem outdegree_pairedGraph_inr
    {V W : Type*} [Fintype V] [Fintype W]
    (G : ℕ → V → V → Prop) (H : ℕ → W → W → Prop)
    (t : ℕ) (w : W) :
    outdegree (pairedGraph G H) t (Sum.inr w) = outdegree H t w := by
  classical
  unfold outdegree
  symm
  apply Set.ncard_congr
    (s := {x : W | H t w x})
    (t := {a : Sum V W | pairedGraph G H t (Sum.inr w) a})
    (fun x _ ↦ Sum.inr x)
  · intro x hx
    simpa [pairedGraph] using hx
  · intro a b ha hb hab
    exact Sum.inr_injective hab
  · intro a ha
    cases a with
    | inl v => simp [pairedGraph] at ha
    | inr x => exact ⟨x, by simpa [pairedGraph] using ha, rfl⟩

/-- Cross-equal successor histories have the same current outdegree in their
respective executions. -/
theorem crossSameHistory_outdegree
    {V W Input : Type*} [Fintype V] [Fintype W]
    {G : ℕ → V → V → Prop} {H : ℕ → W → W → Prop}
    {inputV : V → Input} {inputW : W → Input}
    {t : ℕ} {v : V} {w : W}
    (hcross : crossSameHistory G H inputV inputW (t + 1) v w) :
    outdegree G (t + 1) v = outdegree H (t + 1) w := by
  have hdegree := hcross.2.1
  simpa [outdegree_pairedGraph_inl, outdegree_pairedGraph_inr] using hdegree

/-- Equality of recursive histories is hereditary to every earlier time. -/
theorem sameHistory_of_le {A Input : Type*}
    {K : ℕ → A → A → Prop} {input : A → Input}
    {s t : ℕ} {u v : A} (hst : s ≤ t)
    (h : sameHistory K input t u v) :
    sameHistory K input s u v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih =>
      exact ih (sameHistory_of_succ h)

/-- A temporal information path.  At every round, information may be kept by
the same agent (a black history edge) or sent over a communication arc (a red
history edge). -/
inductive TemporalReach {V : Type*}
    (G : ℕ → V → V → Prop) (start : ℕ) (source : V) : ℕ → V → Prop
  | zero : TemporalReach G start source 0 source
  | stay {k : ℕ} {v : V} :
      TemporalReach G start source k v →
      TemporalReach G start source (k + 1) v
  | send {k : ℕ} {u v : V} :
      TemporalReach G start source k u →
      G (start + k + 1) u v →
      TemporalReach G start source (k + 1) v

/-- Vertices reached by the temporal information path after exactly `k`
rounds, allowing retention in every round. -/
noncomputable def temporalInformed {V : Type*} [Fintype V]
    (G : ℕ → V → V → Prop) (start : ℕ) (source : V) (k : ℕ) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun v ↦ TemporalReach G start source k v

@[simp] theorem mem_temporalInformed {V : Type*} [Fintype V]
    (G : ℕ → V → V → Prop) (start : ℕ) (source : V) (k : ℕ) (v : V) :
    v ∈ temporalInformed G start source k ↔
      TemporalReach G start source k v := by
  classical
  simp [temporalInformed]

/-- In a sequence of strongly connected directed graphs, a temporal path
from any source reaches every vertex in at most `|V|-1` rounds. -/
theorem temporalReach_card_sub_one {V : Type*} [Fintype V]
    (G : ℕ → V → V → Prop)
    (hsc : ∀ t, StronglyConnected (G t))
    (start : ℕ) (source target : V) :
    TemporalReach G start source (Nat.card V - 1) target := by
  classical
  letI : Nonempty V := ⟨source⟩
  let informed : ℕ → Finset V := temporalInformed G start source
  let edge : ℕ → V → V → Prop := fun k ↦ G (start + k + 1)
  have hinitial : (informed 0).Nonempty := by
    refine ⟨source, ?_⟩
    simp [informed, TemporalReach.zero]
  have hmono : ∀ k, informed k ⊆ informed (k + 1) := by
    intro k v hv
    have hreach : TemporalReach G start source k v := by
      simpa [informed] using hv
    simpa [informed] using TemporalReach.stay hreach
  have hdeliver : ∀ k ⦃u v : V⦄, u ∈ informed k → edge k u v →
      v ∈ informed (k + 1) := by
    intro k u v hu huv
    have hreach : TemporalReach G start source k u := by
      simpa [informed] using hu
    simpa [informed, edge, Nat.add_assoc] using TemporalReach.send hreach huv
  have hall : informed (Nat.card V - 1) = Finset.univ :=
    directed_flooding edge informed
      (fun k ↦ by simpa [edge, Nat.add_assoc] using hsc (start + k + 1))
      hinitial hmono hdeliver
  have htarget : target ∈ informed (Nat.card V - 1) := by
    rw [hall]
    exact Finset.mem_univ target
  simpa [informed] using htarget

/-- A temporal path visible in a reference history can be transported
backwards through an equal history in the matching execution.

The red-step case is the key point: a reference arc makes the corresponding
received-message class nonempty.  Equality of the two received multisets
therefore supplies an actual matching predecessor in the other execution. -/
theorem exists_cross_origin_of_temporalReach
    {V W Input : Type*} [Fintype V] [Fintype W]
    {G : ℕ → V → V → Prop} {H : ℕ → W → W → Prop}
    {inputV : V → Input} {inputW : W → Input}
    {start k : ℕ} {source target : V} {matchingTarget : W}
    (hreach : TemporalReach G start source k target)
    (hcross : crossSameHistory G H inputV inputW
      (start + k) target matchingTarget) :
    ∃ matchingSource : W,
      crossSameHistory G H inputV inputW start source matchingSource := by
  induction hreach generalizing matchingTarget with
  | zero =>
      simpa using ⟨matchingTarget, hcross⟩
  | @stay k target hreach ih =>
      have hcrossSucc :
          sameHistory (pairedGraph G H) (pairedInput inputV inputW)
            ((start + k) + 1) (Sum.inl target) (Sum.inr matchingTarget) := by
        simpa [crossSameHistory, Nat.add_assoc] using hcross
      have hprevious := sameHistory_of_succ hcrossSucc
      exact ih (by simpa [crossSameHistory] using hprevious)
  | @send k previous target hreach hedge ih =>
      let K := pairedGraph G H
      let input := pairedInput inputV inputW
      have hcrossSucc : sameHistory K input ((start + k) + 1)
          (Sum.inl target) (Sum.inr matchingTarget) := by
        simpa [K, input, crossSameHistory, Nat.add_assoc] using hcross
      have hcounts := hcrossSucc.2.2 (Sum.inl previous)
      let leftSources : Set (Sum V W) :=
        {a | K (start + k + 1) a (Sum.inl target) ∧
          sameHistory K input (start + k) a (Sum.inl previous)}
      let rightSources : Set (Sum V W) :=
        {a | K (start + k + 1) a (Sum.inr matchingTarget) ∧
          sameHistory K input (start + k) a (Sum.inl previous)}
      have hleftNonempty : leftSources.Nonempty := by
        refine ⟨Sum.inl previous, ?_⟩
        exact ⟨by simpa [K, pairedGraph, Nat.add_assoc] using hedge,
          sameHistory_refl K input (start + k) (Sum.inl previous)⟩
      have hleftPos : 0 < leftSources.ncard :=
        (Set.ncard_pos).2 hleftNonempty
      have hcountEq : leftSources.ncard = rightSources.ncard := by
        simpa [leftSources, rightSources, K, input, Nat.add_assoc] using hcounts
      have hrightPos : 0 < rightSources.ncard := by
        rw [← hcountEq]
        exact hleftPos
      obtain ⟨a, haEdge, haHistory⟩ :=
        ((Set.ncard_pos).1 hrightPos : rightSources.Nonempty)
      cases a with
      | inl a =>
          simp [K, pairedGraph] at haEdge
      | inr a =>
          have hsourceCross : crossSameHistory G H inputV inputW
              (start + k) previous a := by
            exact sameHistory_symm K input (start + k) _ _ haHistory
          exact ih hsourceCross

/-- **Positive matching-fiber bridge.**

Suppose the designated leaders of two executions have equal histories
through `T`.  Every reference agent's history at a level `start` lying at
least `|V|-1` rounds before `T` then occurs in the matching execution.  This
is the concrete positivity fact required by `RefinementData.zOld_pos` and
`RefinementData.zNew_pos`; it is no longer an abstract certificate field. -/
theorem exists_cross_match_of_equal_leaders
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : ℕ → V → V → Prop) (H : ℕ → W → W → Prop)
    (inputV : V → Input) (inputW : W → Input)
    (leaderV : V) (leaderW : W)
    (hscG : ∀ t, StronglyConnected (G t))
    {start T : ℕ}
    (hvisible : start + (Nat.card V - 1) ≤ T)
    (hleaders : crossSameHistory G H inputV inputW T leaderV leaderW)
    (source : V) :
    ∃ matchingSource : W,
      crossSameHistory G H inputV inputW start source matchingSource := by
  let delay := Nat.card V - 1
  have hreach : TemporalReach G start source delay leaderV :=
    temporalReach_card_sub_one G hscG start source leaderV
  have hleaderEarlier : crossSameHistory G H inputV inputW
      (start + delay) leaderV leaderW := by
    exact sameHistory_of_le hvisible hleaders
  exact exists_cross_origin_of_temporalReach hreach hleaderEarlier

end DirectedCounting
