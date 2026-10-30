import DirectedCountingFormalization.MultigraphHistoryModel
import DirectedCountingFormalization.PairedHistory
import Mathlib.Tactic

set_option warningAsError true

/-!
# Shared histories of two multigraph executions

This is the multiplicity-preserving counterpart of `PairedHistory.lean`.
Its main theorem transports every sufficiently early reference history
through equality of two arbitrary terminal roots.  This supplies positivity
of all matching fibers without assuming that either observed root is the
leader.
-/

namespace DirectedCounting

/-- Outdegree in the left component of a paired multigraph is unchanged. -/
theorem multigraphOutdegree_paired_inl
    {V W : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (t : Nat) (v : V) :
    multigraphOutdegree (pairedMultigraph G H) t (Sum.inl v) =
      multigraphOutdegree G t v := by
  classical
  unfold multigraphOutdegree
  rw [Fintype.sum_sum_type]
  simp [pairedMultigraph]

/-- Outdegree in the right component of a paired multigraph is unchanged. -/
theorem multigraphOutdegree_paired_inr
    {V W : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (t : Nat) (w : W) :
    multigraphOutdegree (pairedMultigraph G H) t (Sum.inr w) =
      multigraphOutdegree H t w := by
  classical
  unfold multigraphOutdegree
  rw [Fintype.sum_sum_type]
  simp [pairedMultigraph]

/-- Multigraph history equality is hereditary to every earlier level. -/
theorem sameMultigraphHistory_of_le
    {A Input : Type*} [Fintype A]
    {K : Nat → A → A → Nat} {input : A → Input}
    {s t : Nat} {u v : A} (hst : s ≤ t)
    (h : sameMultigraphHistory K input t u v) :
    sameMultigraphHistory K input s u v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (sameMultigraphHistory_of_succ h)

/-- A temporal support path in the reference multigraph can be transported
backward through an equal history in the matching execution. -/
theorem exists_cross_multigraph_origin_of_temporalReach
    {V W Input : Type*} [Fintype V] [Fintype W]
    {G : Nat → V → V → Nat} {H : Nat → W → W → Nat}
    {inputV : V → Input} {inputW : W → Input}
    {start k : Nat} {source target : V} {matchingTarget : W}
    (hreach : TemporalReach (fun t u v ↦ 0 < G t u v)
      start source k target)
    (hcross : crossSameMultigraphHistory G H inputV inputW
      (start + k) target matchingTarget) :
    ∃ matchingSource : W,
      crossSameMultigraphHistory G H inputV inputW
        start source matchingSource := by
  induction hreach generalizing matchingTarget with
  | zero => simpa using ⟨matchingTarget, hcross⟩
  | @stay k target hreach ih =>
      have hcrossSucc :
          sameMultigraphHistory (pairedMultigraph G H)
            (pairedMultigraphInput inputV inputW) ((start + k) + 1)
            (Sum.inl target) (Sum.inr matchingTarget) := by
        simpa [crossSameMultigraphHistory, Nat.add_assoc] using hcross
      have hprevious := sameMultigraphHistory_of_succ hcrossSucc
      exact ih (by simpa [crossSameMultigraphHistory] using hprevious)
  | @send k previous target hreach hedge ih =>
      let K := pairedMultigraph G H
      let input := pairedMultigraphInput inputV inputW
      have hcrossSucc : sameMultigraphHistory K input ((start + k) + 1)
          (Sum.inl target) (Sum.inr matchingTarget) := by
        simpa [K, input, crossSameMultigraphHistory, Nat.add_assoc] using hcross
      have hcounts := hcrossSucc.2.2 (Sum.inl previous)
      have hleftPos :
          0 < weightedIncomingFromClass (K (start + k + 1))
            (sameMultigraphHistory K input (start + k))
            (Sum.inl target) (Sum.inl previous) := by
        apply (weightedIncomingFromClass_pos_iff _ _ _ _).2
        refine ⟨Sum.inl previous,
          sameMultigraphHistory_refl K input (start + k) _, ?_⟩
        simpa [K, pairedMultigraph, Nat.add_assoc] using hedge
      have hrightPos :
          0 < weightedIncomingFromClass (K (start + k + 1))
            (sameMultigraphHistory K input (start + k))
            (Sum.inr matchingTarget) (Sum.inl previous) := by
        rw [← hcounts]
        simpa [Nat.add_assoc] using hleftPos
      obtain ⟨a, haHistory, haEdge⟩ :=
        (weightedIncomingFromClass_pos_iff
          (K (start + k + 1))
          (sameMultigraphHistory K input (start + k))
          (Sum.inr matchingTarget) (Sum.inl previous)).1 hrightPos
      cases a with
      | inl a => simp [K, pairedMultigraph] at haEdge
      | inr a =>
          have hsourceCross : crossSameMultigraphHistory G H inputV inputW
              (start + k) previous a := by
            exact sameMultigraphHistory_symm K input (start + k) _ _ haHistory
          exact ih hsourceCross

/-- **Multigraph positive-fiber bridge.**

If arbitrary designated roots have equal histories through `T`, every
reference history at least `|V|-1` rounds earlier occurs in the matching
execution.  Connectivity is required only of the positive-multiplicity
support of each reference round. -/
theorem exists_cross_multigraph_match_of_equal_roots
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input)
    (rootV : V) (rootW : W)
    (hscG : ∀ t, MultigraphRoundConnected G t)
    {start T : Nat}
    (hvisible : start + (Nat.card V - 1) ≤ T)
    (hroots : crossSameMultigraphHistory G H inputV inputW
      T rootV rootW)
    (source : V) :
    ∃ matchingSource : W,
      crossSameMultigraphHistory G H inputV inputW
        start source matchingSource := by
  let support : Nat → V → V → Prop := fun t u v ↦ 0 < G t u v
  let delay := Nat.card V - 1
  have hreach : TemporalReach support start source delay rootV :=
    temporalReach_card_sub_one support hscG start source rootV
  have hrootEarlier : crossSameMultigraphHistory G H inputV inputW
      (start + delay) rootV rootW :=
    sameMultigraphHistory_of_le hvisible hroots
  exact exists_cross_multigraph_origin_of_temporalReach hreach hrootEarlier

end DirectedCounting
