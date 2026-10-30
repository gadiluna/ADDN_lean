import DirectedCountingFormalization.MultigraphPairedHistory
import DirectedCountingFormalization.CrossExecutionPotential
import Mathlib.Tactic

set_option warningAsError true

/-!
# Concrete paired refinements for dynamic multigraph histories

This module is the multiplicity-preserving counterpart of
`PairedRefinement.lean`.  Reference classes are quotient classes of the
reference carrier under multigraph-history equality in the disjoint-union
execution.  Their matching fibers contain exactly the agents of the second
execution with the same (weighted) history.

No support-graph or Boolean reduction occurs here: every quotient is formed
using `sameMultigraphHistory`, whose incoming coordinates sum the full
natural-valued edge multiplicities.
-/

namespace DirectedCounting

open scoped BigOperators

/-- History equivalence on the reference carrier, computed in the paired
multigraph execution. -/
noncomputable def multigraphReferenceHistorySetoid
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) : Setoid V where
  r u v := sameMultigraphHistory (pairedMultigraph G H)
    (pairedMultigraphInput inputV inputW) t (Sum.inl u) (Sum.inl v)
  iseqv :=
    ⟨fun v ↦ sameMultigraphHistory_refl _ _ t (Sum.inl v),
      fun h ↦ sameMultigraphHistory_symm _ _ t _ _ h,
      fun h₁ h₂ ↦ sameMultigraphHistory_trans _ _ t _ _ _ h₁ h₂⟩

/-- Reference multigraph-history classes at time `t`. -/
abbrev MultigraphReferenceHistoryClass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :=
  Quotient (multigraphReferenceHistorySetoid G H inputV inputW t)

noncomputable instance multigraphReferenceHistoryClassFintype
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    Fintype (MultigraphReferenceHistoryClass G H inputV inputW t) :=
  Fintype.ofFinite _

noncomputable instance multigraphReferenceHistoryClassDecidableEq
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    DecidableEq (MultigraphReferenceHistoryClass G H inputV inputW t) :=
  Classical.decEq _

/-- Embed a reference quotient class in the paired multigraph-history
partition. -/
noncomputable def multigraphReferenceToPairedClass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    MultigraphReferenceHistoryClass G H inputV inputW t →
      MultigraphHistoryClass (pairedMultigraph G H)
        (pairedMultigraphInput inputV inputW) t :=
  Quotient.map Sum.inl (fun _ _ h ↦ h)

@[simp] theorem multigraphReferenceToPairedClass_mk
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) (v : V) :
    multigraphReferenceToPairedClass G H inputV inputW t (Quotient.mk'' v) =
      Quotient.mk'' (Sum.inl v) := rfl

/-- Distinct reference classes remain distinct in the paired partition. -/
theorem multigraphReferenceToPairedClass_injective
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    Function.Injective
      (multigraphReferenceToPairedClass G H inputV inputW t) := by
  intro a b hab
  refine Quotient.inductionOn₂ a b ?_ hab
  intro u v huv
  have hpaired :
      (Quotient.mk'' (Sum.inl u) :
        MultigraphHistoryClass (pairedMultigraph G H)
          (pairedMultigraphInput inputV inputW) t) =
      Quotient.mk'' (Sum.inl v) := by
    simpa using huv
  have hrel := Quotient.exact
    (s := multigraphHistorySetoid (pairedMultigraph G H)
      (pairedMultigraphInput inputV inputW) t) hpaired
  apply Quotient.sound
  exact hrel

/-- Forgetting the newest round maps a reference child to its parent. -/
noncomputable def forgetMultigraphReferenceHistoryClass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    MultigraphReferenceHistoryClass G H inputV inputW (t + 1) →
      MultigraphReferenceHistoryClass G H inputV inputW t :=
  Quotient.map id (fun _ _ h ↦ sameMultigraphHistory_of_succ h)

@[simp] theorem forgetMultigraphReferenceHistoryClass_mk
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) (v : V) :
    forgetMultigraphReferenceHistoryClass G H inputV inputW t
        (Quotient.mk'' v) =
      Quotient.mk'' v := rfl

/-- The finite reference fiber underlying a reference class. -/
noncomputable def multigraphReferenceClassFinset
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦
    (Quotient.mk'' v :
      MultigraphReferenceHistoryClass G H inputV inputW t) = c

/-- Number of reference agents in a reference multigraph-history class. -/
noncomputable def multigraphReferenceClassMass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) : Nat :=
  (multigraphReferenceClassFinset G H inputV inputW t c).card

@[simp] theorem multigraphReferenceClassFinset_card
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) :
    (multigraphReferenceClassFinset G H inputV inputW t c).card =
      multigraphReferenceClassMass G H inputV inputW t c := rfl

/-- Distinct reference quotient classes have disjoint reference fibers. -/
theorem multigraphReferenceClassFinsets_pairwiseDisjoint
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    ((Finset.univ : Finset
      (MultigraphReferenceHistoryClass G H inputV inputW t)) : Set _).PairwiseDisjoint
        (multigraphReferenceClassFinset G H inputV inputW t) := by
  intro i _ j _ hij
  change Disjoint (multigraphReferenceClassFinset G H inputV inputW t i)
    (multigraphReferenceClassFinset G H inputV inputW t j)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hvi' : (Quotient.mk'' v :
      MultigraphReferenceHistoryClass G H inputV inputW t) = i := by
    simpa [multigraphReferenceClassFinset] using hvi
  have hvj' : (Quotient.mk'' v :
      MultigraphReferenceHistoryClass G H inputV inputW t) = j := by
    simpa [multigraphReferenceClassFinset] using hvj
  exact hij (hvi'.symm.trans hvj')

/-- The reference fibers cover the whole reference carrier. -/
theorem biUnion_multigraphReferenceClassFinset_eq_univ
    {V W Input : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    (Finset.univ : Finset
      (MultigraphReferenceHistoryClass G H inputV inputW t)).biUnion
        (multigraphReferenceClassFinset G H inputV inputW t) =
      (Finset.univ : Finset V) := by
  apply Finset.eq_univ_of_forall
  intro v
  simp only [Finset.mem_biUnion]
  refine ⟨(Quotient.mk'' v :
    MultigraphReferenceHistoryClass G H inputV inputW t),
    Finset.mem_univ _, ?_⟩
  simp [multigraphReferenceClassFinset]

/-- The finite matching fiber represented by a reference class. -/
noncomputable def multigraphMatchingClassFinset
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) : Finset W := by
  classical
  exact Finset.univ.filter fun w ↦
    (Quotient.mk'' (Sum.inr w) :
      MultigraphHistoryClass (pairedMultigraph G H)
        (pairedMultigraphInput inputV inputW) t) =
      multigraphReferenceToPairedClass G H inputV inputW t c

/-- Number of matching agents with the represented reference history. -/
noncomputable def multigraphMatchingClassMass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) : Nat :=
  (multigraphMatchingClassFinset G H inputV inputW t c).card

@[simp] theorem multigraphMatchingClassFinset_card
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) :
    (multigraphMatchingClassFinset G H inputV inputW t c).card =
      multigraphMatchingClassMass G H inputV inputW t c := rfl

/-- Matching fibers represented by distinct reference classes are disjoint. -/
theorem multigraphMatchingClassFinsets_pairwiseDisjoint
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    ((Finset.univ : Finset
      (MultigraphReferenceHistoryClass G H inputV inputW t)) : Set _).PairwiseDisjoint
        (multigraphMatchingClassFinset G H inputV inputW t) := by
  intro i _ j _ hij
  change Disjoint (multigraphMatchingClassFinset G H inputV inputW t i)
    (multigraphMatchingClassFinset G H inputV inputW t j)
  rw [Finset.disjoint_left]
  intro w hwi hwj
  have hwi' :
      (Quotient.mk'' (Sum.inr w) :
        MultigraphHistoryClass (pairedMultigraph G H)
          (pairedMultigraphInput inputV inputW) t) =
      multigraphReferenceToPairedClass G H inputV inputW t i := by
    simpa [multigraphMatchingClassFinset] using hwi
  have hwj' :
      (Quotient.mk'' (Sum.inr w) :
        MultigraphHistoryClass (pairedMultigraph G H)
          (pairedMultigraphInput inputV inputW) t) =
      multigraphReferenceToPairedClass G H inputV inputW t j := by
    simpa [multigraphMatchingClassFinset] using hwj
  apply hij
  exact multigraphReferenceToPairedClass_injective G H inputV inputW t
    (hwi'.symm.trans hwj')

/-- Every reference class has positive reference mass. -/
theorem multigraphReferenceClassMass_pos
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) :
    0 < multigraphReferenceClassMass G H inputV inputW t c := by
  classical
  refine Quotient.inductionOn c ?_
  intro v
  apply Finset.card_pos.mpr
  exact ⟨v, by simp [multigraphReferenceClassFinset]⟩

/-- Membership in a matching quotient fiber is cross-execution weighted
history equality. -/
theorem mem_multigraphMatchingClass_iff_crossSameHistory
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (v : V) (w : W) :
    (Quotient.mk'' (Sum.inr w) :
      MultigraphHistoryClass (pairedMultigraph G H)
        (pairedMultigraphInput inputV inputW) t) =
        multigraphReferenceToPairedClass G H inputV inputW t
          (Quotient.mk'' v) ↔
      crossSameMultigraphHistory G H inputV inputW t v w := by
  change Quotient.mk'' (Sum.inr w) = Quotient.mk'' (Sum.inl v) ↔ _
  rw [Quotient.eq]
  exact ⟨fun h ↦ sameMultigraphHistory_symm _ _ t _ _ h,
    fun h ↦ sameMultigraphHistory_symm _ _ t _ _ h⟩

/-- Equality of arbitrary terminal roots, plus the reference visibility
margin, makes every early reference fiber positive in the matching
execution. -/
theorem multigraphMatchingClassMass_pos_of_equal_roots
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input)
    (rootV : V) (rootW : W)
    (hscG : ∀ t, MultigraphRoundConnected G t)
    {start T : Nat}
    (hvisible : start + (Nat.card V - 1) ≤ T)
    (hroots : crossSameMultigraphHistory G H inputV inputW T rootV rootW)
    (c : MultigraphReferenceHistoryClass G H inputV inputW start) :
    0 < multigraphMatchingClassMass G H inputV inputW start c := by
  classical
  refine Quotient.inductionOn c ?_
  intro v
  obtain ⟨w, hw⟩ := exists_cross_multigraph_match_of_equal_roots
    G H inputV inputW rootV rootW hscG hvisible hroots v
  apply Finset.card_pos.mpr
  refine ⟨w, ?_⟩
  simp only [multigraphMatchingClassFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact (mem_multigraphMatchingClass_iff_crossSameHistory
    G H inputV inputW start v w).2 hw

/-- Reference quotient fibers partition the reference carrier. -/
theorem sum_multigraphReferenceClassMass_eq_card
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat) :
    (∑ c : MultigraphReferenceHistoryClass G H inputV inputW t,
      multigraphReferenceClassMass G H inputV inputW t c) =
      Nat.card V := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset
      (MultigraphReferenceHistoryClass G H inputV inputW t)))
    (f := fun v ↦ (Quotient.mk'' v :
      MultigraphReferenceHistoryClass G H inputV inputW t))
    (fun _ _ ↦ Finset.mem_univ _)
  rw [Nat.card_eq_fintype_card]
  simpa only [multigraphReferenceClassMass,
    multigraphReferenceClassFinset, Finset.card_univ,
    Finset.sum_const_zero, Finset.mem_univ, Finset.filter_true] using
      hpartition.symm

/-- Reference class mass is conserved exactly through the parent map. -/
theorem multigraphReferenceClassMass_conserve
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) :
    fiberMass (forgetMultigraphReferenceHistoryClass G H inputV inputW t)
        (multigraphReferenceClassMass G H inputV inputW (t + 1)) c =
      multigraphReferenceClassMass G H inputV inputW t c := by
  classical
  unfold fiberMass multigraphReferenceClassMass multigraphReferenceClassFinset
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp [refinementFiber]

/-- The reference-class embedding commutes with forgetting one round. -/
theorem forget_multigraphReferenceToPairedClass
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW (t + 1)) :
    forgetMultigraphHistoryClass (pairedMultigraph G H)
        (pairedMultigraphInput inputV inputW) t
        (multigraphReferenceToPairedClass G H inputV inputW (t + 1) c) =
      multigraphReferenceToPairedClass G H inputV inputW t
        (forgetMultigraphReferenceHistoryClass G H inputV inputW t c) := by
  refine Quotient.inductionOn c ?_
  intro v
  rfl

/-- Membership in a represented matching child implies membership in its
represented matching parent. -/
theorem multigraphMatching_child_implies_parent
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW (t + 1))
    (w : W)
    (hmatch :
      (Quotient.mk'' (Sum.inr w) :
        MultigraphHistoryClass (pairedMultigraph G H)
          (pairedMultigraphInput inputV inputW) (t + 1)) =
        multigraphReferenceToPairedClass G H inputV inputW (t + 1) c) :
    (Quotient.mk'' (Sum.inr w) :
      MultigraphHistoryClass (pairedMultigraph G H)
        (pairedMultigraphInput inputV inputW) t) =
      multigraphReferenceToPairedClass G H inputV inputW t
        (forgetMultigraphReferenceHistoryClass G H inputV inputW t c) := by
  have hforgotten := congrArg
    (forgetMultigraphHistoryClass (pairedMultigraph G H)
      (pairedMultigraphInput inputV inputW) t) hmatch
  rw [forget_multigraphReferenceToPairedClass] at hforgotten
  exact hforgotten

/-- A represented matching child fiber is contained in its parent fiber. -/
theorem multigraphMatchingClassFinset_subset_parent
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW (t + 1)) :
    multigraphMatchingClassFinset G H inputV inputW (t + 1) c ⊆
      multigraphMatchingClassFinset G H inputV inputW t
        (forgetMultigraphReferenceHistoryClass G H inputV inputW t c) := by
  intro w hw
  have hmatch :
      (Quotient.mk'' (Sum.inr w) :
        MultigraphHistoryClass (pairedMultigraph G H)
          (pairedMultigraphInput inputV inputW) (t + 1)) =
      multigraphReferenceToPairedClass G H inputV inputW (t + 1) c := by
    simpa [multigraphMatchingClassFinset] using hw
  have hparent := multigraphMatching_child_implies_parent
    G H inputV inputW t c w hmatch
  simpa [multigraphMatchingClassFinset] using hparent

/-- Equality of a child and parent matching mass upgrades containment to
equality of the underlying finite fibers. -/
theorem multigraphMatchingClassFinset_eq_parent_of_mass_eq
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW (t + 1))
    (hmass : multigraphMatchingClassMass G H inputV inputW t
        (forgetMultigraphReferenceHistoryClass G H inputV inputW t c) =
      multigraphMatchingClassMass G H inputV inputW (t + 1) c) :
    multigraphMatchingClassFinset G H inputV inputW (t + 1) c =
      multigraphMatchingClassFinset G H inputV inputW t
        (forgetMultigraphReferenceHistoryClass G H inputV inputW t c) := by
  apply Finset.eq_of_subset_of_card_le
    (multigraphMatchingClassFinset_subset_parent
      G H inputV inputW t c)
  simpa only [multigraphMatchingClassFinset_card] using hmass.le

/-- Matching mass is subconserved because matching agents can leave the
represented reference histories but cannot enter a different parent fiber. -/
theorem multigraphMatchingClassMass_subconserve
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input) (t : Nat)
    (c : MultigraphReferenceHistoryClass G H inputV inputW t) :
    fiberMass (forgetMultigraphReferenceHistoryClass G H inputV inputW t)
        (multigraphMatchingClassMass G H inputV inputW (t + 1)) c ≤
      multigraphMatchingClassMass G H inputV inputW t c := by
  classical
  let Old := MultigraphReferenceHistoryClass G H inputV inputW t
  let New := MultigraphReferenceHistoryClass G H inputV inputW (t + 1)
  let parent : New → Old :=
    forgetMultigraphReferenceHistoryClass G H inputV inputW t
  let children : Finset New := refinementFiber parent c
  let childMatching : New → Finset W := fun j ↦
    multigraphMatchingClassFinset G H inputV inputW (t + 1) j
  let oldMatching : Finset W :=
    multigraphMatchingClassFinset G H inputV inputW t c
  have hdisjoint : (children : Set New).PairwiseDisjoint childMatching := by
    intro i _ j _ hij
    exact multigraphMatchingClassFinsets_pairwiseDisjoint
      G H inputV inputW (t + 1) (Finset.mem_univ i)
        (Finset.mem_univ j) hij
  have hunionSubset : children.biUnion childMatching ⊆ oldMatching := by
    intro w hw
    simp only [Finset.mem_biUnion] at hw
    obtain ⟨j, hjChild, hwj⟩ := hw
    have hjParent : parent j = c := by
      simpa [children, refinementFiber] using hjChild
    have hwParent := multigraphMatchingClassFinset_subset_parent
      G H inputV inputW t j hwj
    simpa [oldMatching, parent, hjParent] using hwParent
  have hcardUnion : (children.biUnion childMatching).card =
      ∑ j ∈ children, (childMatching j).card :=
    Finset.card_biUnion hdisjoint
  have hcardLe : (children.biUnion childMatching).card ≤
      oldMatching.card := Finset.card_le_card hunionSubset
  unfold fiberMass multigraphMatchingClassMass
  change (∑ j ∈ children, (childMatching j).card) ≤ oldMatching.card
  rw [← hcardUnion]
  exact hcardLe

/-- Adjacent paired multigraph-history partitions instantiate the abstract
cross-execution refinement data.  Positivity follows from equal arbitrary
terminal roots and the `|V|-1` visibility margin. -/
noncomputable def multigraphPairedRefinementData
    {V W Input : Type*} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (inputV : V → Input) (inputW : W → Input)
    (rootV : V) (rootW : W)
    (hscG : ∀ s, MultigraphRoundConnected G s)
    (t T : Nat)
    (hvisible : (t + 1) + (Nat.card V - 1) ≤ T)
    (hroots : crossSameMultigraphHistory G H inputV inputW T rootV rootW) :
    RefinementData
      (MultigraphReferenceHistoryClass G H inputV inputW t)
      (MultigraphReferenceHistoryClass G H inputV inputW (t + 1)) := by
  classical
  have hvisibleOld : t + (Nat.card V - 1) ≤ T := by omega
  exact
    { parent := forgetMultigraphReferenceHistoryClass G H inputV inputW t
      yOld := multigraphReferenceClassMass G H inputV inputW t
      zOld := multigraphMatchingClassMass G H inputV inputW t
      yNew := multigraphReferenceClassMass G H inputV inputW (t + 1)
      zNew := multigraphMatchingClassMass G H inputV inputW (t + 1)
      yOld_pos := fun c ↦
        multigraphReferenceClassMass_pos G H inputV inputW t c
      zOld_pos := fun c ↦
        multigraphMatchingClassMass_pos_of_equal_roots
          G H inputV inputW rootV rootW hscG hvisibleOld hroots c
      yNew_pos := fun c ↦
        multigraphReferenceClassMass_pos G H inputV inputW (t + 1) c
      zNew_pos := fun c ↦
        multigraphMatchingClassMass_pos_of_equal_roots
          G H inputV inputW rootV rootW hscG hvisible hroots c
      y_conserve := fun c ↦
        multigraphReferenceClassMass_conserve
          G H inputV inputW t c
      z_subconserve := fun c ↦
        multigraphMatchingClassMass_subconserve
          G H inputV inputW t c }

end DirectedCounting
