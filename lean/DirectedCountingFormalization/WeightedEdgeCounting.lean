import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option warningAsError true

/-!
# Finite edge double counting with natural multiplicities

These lemmas are the multigraph analogue of `EdgeCounting.lean`.  The edge
function records an arbitrary natural multiplicity, so parallel links and
self-loops are retained exactly.
-/

namespace DirectedCounting

open scoped BigOperators

/-- Multiplicity entering one target from a finite source set. -/
def weightedIncomingCount {A B : Type*}
    (edge : A → B → Nat) (sources : Finset A) (target : B) : Nat :=
  ∑ source ∈ sources, edge source target

/-- Total edge multiplicity between two finite sets, enumerated by target. -/
def weightedEdgeCount {A B : Type*}
    (edge : A → B → Nat) (sources : Finset A) (targets : Finset B) : Nat :=
  ∑ target ∈ targets, weightedIncomingCount edge sources target

/-- Swapping source and target enumeration transposes the multiplicity
matrix but leaves the total unchanged. -/
theorem weightedEdgeCount_transpose {A B : Type*}
    (edge : A → B → Nat) (sources : Finset A) (targets : Finset B) :
    weightedEdgeCount edge sources targets =
      weightedEdgeCount (fun v u ↦ edge u v) targets sources := by
  classical
  unfold weightedEdgeCount weightedIncomingCount
  rw [Finset.sum_comm]

/-- Symmetric multiplicities give the usual undirected cut identity. -/
theorem weightedEdgeCount_symm {A : Type*}
    (edge : A → A → Nat) (hsymm : ∀ u v, edge u v = edge v u)
    (left right : Finset A) :
    weightedEdgeCount edge left right = weightedEdgeCount edge right left := by
  rw [weightedEdgeCount_transpose]
  apply Finset.sum_congr rfl
  intro u hu
  unfold weightedIncomingCount
  apply Finset.sum_congr rfl
  intro v hv
  exact hsymm u v

/-- Constant incoming multiplicity on a target fiber multiplies by the
fiber's cardinality. -/
theorem weightedEdgeCount_eq_mul_card_of_constant_incoming
    {A B : Type*} (edge : A → B → Nat)
    (sources : Finset A) (targets : Finset B) (multiplicity : Nat)
    (hconstant : ∀ v ∈ targets,
      weightedIncomingCount edge sources v = multiplicity) :
    weightedEdgeCount edge sources targets = multiplicity * targets.card := by
  classical
  unfold weightedEdgeCount
  calc
    (∑ v ∈ targets, weightedIncomingCount edge sources v) =
        ∑ _v ∈ targets, multiplicity := Finset.sum_congr rfl hconstant
    _ = targets.card * multiplicity :=
      Finset.sum_const_nat (fun _ _ ↦ rfl)
    _ = multiplicity * targets.card := Nat.mul_comm _ _

/-- Weighted edge counting distributes over pairwise-disjoint target
fibers. -/
theorem weightedEdgeCount_biUnion {A B I : Type*} [DecidableEq B]
    (edge : A → B → Nat) (sources : Finset A)
    (indices : Finset I) (targets : I → Finset B)
    (hdisjoint : (indices : Set I).PairwiseDisjoint targets) :
    weightedEdgeCount edge sources (indices.biUnion targets) =
      ∑ i ∈ indices, weightedEdgeCount edge sources (targets i) := by
  classical
  unfold weightedEdgeCount
  exact Finset.sum_biUnion hdisjoint

/-- Enlarging the source set cannot reduce weighted incoming multiplicity. -/
theorem weightedIncomingCount_mono_sources {A B : Type*}
    (edge : A → B → Nat) {small large : Finset A} (target : B)
    (hsubset : small ⊆ large) :
    weightedIncomingCount edge small target ≤
      weightedIncomingCount edge large target := by
  unfold weightedIncomingCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun _ _ _ ↦ Nat.zero_le _)

/-- Enlarging the target set cannot reduce total weighted edge count. -/
theorem weightedEdgeCount_mono_targets {A B : Type*}
    (edge : A → B → Nat) (sources : Finset A)
    {small large : Finset B} (hsubset : small ⊆ large) :
    weightedEdgeCount edge sources small ≤
      weightedEdgeCount edge sources large := by
  unfold weightedEdgeCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun _ _ _ ↦ Nat.zero_le _)

/-- Enlarging both endpoints preserves monotonicity. -/
theorem weightedEdgeCount_mono {A B : Type*}
    (edge : A → B → Nat)
    {smallSources largeSources : Finset A}
    {smallTargets largeTargets : Finset B}
    (hsources : smallSources ⊆ largeSources)
    (htargets : smallTargets ⊆ largeTargets) :
    weightedEdgeCount edge smallSources smallTargets ≤
      weightedEdgeCount edge largeSources largeTargets := by
  calc
    weightedEdgeCount edge smallSources smallTargets ≤
        weightedEdgeCount edge largeSources smallTargets := by
      unfold weightedEdgeCount
      apply Finset.sum_le_sum
      intro target htarget
      exact weightedIncomingCount_mono_sources edge target hsources
    _ ≤ weightedEdgeCount edge largeSources largeTargets :=
      weightedEdgeCount_mono_targets edge largeSources htargets

end DirectedCounting
