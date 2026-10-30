import DirectedCountingFormalization.StrongConnectivityCheck
import DirectedCountingFormalization.LocalBranchingPrefixBridge

/-!
# Executable checker for a branch-aware prefix witness

This file contains only finite data and bounded loops.  A witness records the
candidate weights which a deterministic implementation obtains from its last
nonbranching Perron--Frobenius anchor.  The checker does not enumerate graph
executions, compatible orders, frontier subsets, or integer profiles.

The semantic meaning of an accepted witness is supplied separately by
`LocalBranchingPrefixBridge`: this file deliberately cannot mention the real
network order or the real sizes of visible history classes.
-/

set_option warningAsError true

namespace DirectedCounting

/-- Finite information read from the layered DAG of one local history view,
together with an explicit positive integral candidate profile.  Values at
levels above `R` are irrelevant; total functions keep dependent indexing
simple and make the checker directly executable. -/
structure BranchAwarePrefixWitness (candidate R : Nat) where
  classCount : Nat → Nat
  parent : (h : Nat) → Fin (classCount (h + 1)) → Fin (classCount h)
  degree : (h : Nat) → Fin (classCount (h + 1)) → Nat
  redMultiplicity : (h : Nat) →
    Fin (classCount h) → Fin (classCount (h + 1)) → Nat
  leader : (h : Nat) → Fin (classCount h)
  weight : (h : Nat) → Fin (classCount h) → Nat

namespace BranchAwarePrefixWitness

variable {candidate R : Nat} (W : BranchAwarePrefixWitness candidate R)

/-- Candidate mass carried by the visible children of one old black class. -/
def blackFiberMass (h : Nat) (i : Fin (W.classCount h)) : Nat :=
  ∑ j : Fin (W.classCount (h + 1)),
    if W.parent h j = i then W.weight (h + 1) j else 0

theorem blackFiberMass_eq_fiberMass (h : Nat)
    (i : Fin (W.classCount h)) :
    W.blackFiberMass h i =
      fiberMass (W.parent h) (W.weight (h + 1)) i := by
  unfold blackFiberMass fiberMass refinementFiber
  rw [Finset.sum_filter]

/-- Number of red arcs from one old class into all represented target
classes, evaluated at the candidate target profile. -/
def redRowMass (h : Nat) (i : Fin (W.classCount h)) : Nat :=
  ∑ j : Fin (W.classCount (h + 1)),
    W.redMultiplicity h i j * W.weight (h + 1) j

/-- Number of arcs emitted by represented children of one old black class,
evaluated from the late-aware degree labels. -/
def emittedFiberMass (h : Nat) (i : Fin (W.classCount h)) : Nat :=
  ∑ j : Fin (W.classCount (h + 1)),
    if W.parent h j = i then
      W.degree h j * W.weight (h + 1) j
    else 0

/-- Support of the square target-aligned matrix on a nonbranching level.
Writing it through the parent map avoids computing an inverse permutation. -/
def contractedSupport (h : Nat)
    (source target : Fin (W.classCount h)) : Bool :=
  decide (∃ j : Fin (W.classCount (h + 1)),
    W.parent h j = target ∧ 0 < W.redMultiplicity h source j)

def parentSurjectiveAt (h : Nat) : Prop :=
  ∀ i : Fin (W.classCount h),
    ∃ j : Fin (W.classCount (h + 1)), W.parent h j = i

instance (h : Nat) : Decidable (W.parentSurjectiveAt h) := by
  unfold parentSurjectiveAt
  infer_instance

def blackConservesAt (h : Nat) : Prop :=
  ∀ i : Fin (W.classCount h),
    W.blackFiberMass h i = W.weight h i

instance (h : Nat) : Decidable (W.blackConservesAt h) := by
  unfold blackConservesAt
  infer_instance

def nonbranchingAt (h : Nat) : Prop :=
  W.classCount (h + 1) = W.classCount h

instance (h : Nat) : Decidable (W.nonbranchingAt h) := by
  unfold nonbranchingAt
  infer_instance

/-- All locally checkable Perron--Frobenius premises for one nonbranching
transition.  Balance is written in rectangular parent-map form; when the
checked parent map is surjective and the two finite cardinalities agree, it
is exactly the usual square equation after reindexing targets. -/
def anchorValidAt (h : Nat) : Prop :=
  (∀ j : Fin (W.classCount (h + 1)), 0 < W.degree h j) ∧
  strongConnectivityCheck (W.contractedSupport h) = true ∧
  ∀ i : Fin (W.classCount h),
    W.redRowMass h i = W.emittedFiberMass h i

instance (h : Nat) : Decidable (W.anchorValidAt h) := by
  unfold anchorValidAt
  infer_instance

/-- The finite, proof-carrying local predicate.  Every quantifier ranges over
`Fin R`, a frontier, or a matrix row/column, so evaluation is a bounded
computation. -/
structure Valid : Prop where
  two_le_candidate : 2 ≤ candidate
  certificate_length : 2 * candidate - 2 ≤ R
  initial_class_count : W.classCount 0 = 2
  initial_mass : (∑ i : Fin (W.classCount 0), W.weight 0 i) = candidate
  positive : ∀ h : Fin (R + 1),
    ∀ i : Fin (W.classCount h.1), 0 < W.weight h.1 i
  leader_weight : ∀ h : Fin (R + 1), W.weight h.1 (W.leader h.1) = 1
  parent_surjective : ∀ h : Fin R, W.parentSurjectiveAt h.1
  leader_preserved : ∀ h : Fin R,
    W.parent h.1 (W.leader (h.1 + 1)) = W.leader h.1
  black_conservation : ∀ h : Fin R, W.blackConservesAt h.1
  anchors : ∀ h : Fin R, W.nonbranchingAt h.1 → W.anchorValidAt h.1

/-- Conjunctive presentation used solely to obtain a computational
`Decidable` instance.  Keeping `Valid` as a named structure makes semantic
proofs readable, while this proposition compiles to the same bounded loops. -/
def validRaw : Prop :=
  2 ≤ candidate ∧
  2 * candidate - 2 ≤ R ∧
  W.classCount 0 = 2 ∧
  (∑ i : Fin (W.classCount 0), W.weight 0 i) = candidate ∧
  (∀ h : Fin (R + 1),
    ∀ i : Fin (W.classCount h.1), 0 < W.weight h.1 i) ∧
  (∀ h : Fin (R + 1), W.weight h.1 (W.leader h.1) = 1) ∧
  (∀ h : Fin R, W.parentSurjectiveAt h.1) ∧
  (∀ h : Fin R,
    W.parent h.1 (W.leader (h.1 + 1)) = W.leader h.1) ∧
  (∀ h : Fin R, W.blackConservesAt h.1) ∧
  (∀ h : Fin R, W.nonbranchingAt h.1 → W.anchorValidAt h.1)

instance : Decidable W.validRaw := by
  unfold validRaw
  infer_instance

theorem validRaw_iff : W.validRaw ↔ W.Valid := by
  constructor
  · rintro ⟨hcandidate, hlength, hclasses, hmass, hpositive,
      hleader, hsurjective, hleaderParent, hconserve, hanchors⟩
    exact
      { two_le_candidate := hcandidate
        certificate_length := hlength
        initial_class_count := hclasses
        initial_mass := hmass
        positive := hpositive
        leader_weight := hleader
        parent_surjective := hsurjective
        leader_preserved := hleaderParent
        black_conservation := hconserve
        anchors := hanchors }
  · intro h
    exact ⟨h.two_le_candidate, h.certificate_length,
      h.initial_class_count, h.initial_mass, h.positive, h.leader_weight,
      h.parent_surjective, h.leader_preserved, h.black_conservation,
      h.anchors⟩

/-- Executable Boolean checker for a supplied witness. -/
def check : Bool := decide W.validRaw

theorem check_eq_true_iff : W.check = true ↔ W.Valid := by
  rw [check, decide_eq_true_eq, W.validRaw_iff]

theorem valid_of_check (hcheck : W.check = true) : W.Valid :=
  W.check_eq_true_iff.mp hcheck

/-- Exact black conservation preserves the sum of all candidate weights. -/
theorem weight_total_step (h : Nat) (hconserve : W.blackConservesAt h) :
    (∑ i : Fin (W.classCount h), W.weight h i) =
      ∑ j : Fin (W.classCount (h + 1)), W.weight (h + 1) j := by
  calc
    (∑ i : Fin (W.classCount h), W.weight h i) =
        ∑ i : Fin (W.classCount h), W.blackFiberMass h i := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact (hconserve i).symm
    _ = ∑ j : Fin (W.classCount (h + 1)), W.weight (h + 1) j := by
      simp only [blackFiberMass]
      rw [Finset.sum_comm]
      simp

/-- Hence the checked initial mass is the mass of every selected frontier. -/
theorem weight_total_of_valid (valid : W.Valid) (h : Nat) (hh : h ≤ R) :
    (∑ i : Fin (W.classCount h), W.weight h i) = candidate := by
  induction h with
  | zero => exact valid.initial_mass
  | succ h ih =>
      have hhR : h < R := by omega
      have hstep := W.weight_total_step h
        (valid.black_conservation ⟨h, hhR⟩)
      rw [← hstep]
      exact ih (by omega)

/-! ## Adapter to the arithmetic certificate interface -/

/-- A successful finite check constructs exactly the locally checkable half
of the semantic bridge.  In particular, no real network order or real class
size appears in this construction. -/
def toLocalBranchingPrefixData (valid : W.Valid) :
    LocalBranchingPrefixData candidate R where
  two_le_candidate := valid.two_le_candidate
  classCount := W.classCount
  weight := W.weight
  parent := W.parent
  weight_pos := by
    intro h hh i
    exact valid.positive ⟨h, Nat.lt_succ_iff.mpr hh⟩ i
  weight_total := by
    intro h hh
    exact W.weight_total_of_valid valid h hh
  weight_conserve := by
    intro h hh i
    rw [← W.blackFiberMass_eq_fiberMass h i]
    exact valid.black_conservation ⟨h, hh⟩ i
  initial_classes := valid.initial_class_count
  certificate_length := valid.certificate_length

/-- The checker classifies a transition as branching exactly by a strict
increase in the number of visible history classes. -/
def branchingAt (h : Nat) : Prop :=
  W.classCount h < W.classCount (h + 1)

end BranchAwarePrefixWitness

end DirectedCounting
