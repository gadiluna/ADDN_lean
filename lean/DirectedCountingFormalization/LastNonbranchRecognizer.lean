import DirectedCountingFormalization.BranchAwarePrefixCheck

/-!
# Deterministic completion after the last nonbranching anchor

This file isolates the purely combinatorial part of a last-anchor recognizer.
An external exact linear-algebra routine may provide the positive integral
weights at the last nonbranching frontier.  No trust is placed in that
routine: its proposed vector is checked by `BranchAwarePrefixCheck`.  Here we
show that the remaining all-branching suffix can be completed without any
profile enumeration.

The terminal leaves below an anchor class must each receive positive integral
mass.  This is possible exactly when the anchor mass is at least the number
of terminal descendants.  The canonical construction gives every leaf mass
one and puts the residual on the least leaf of its anchor fiber.  Intermediate
weights are then obtained by summing terminal weights over descendants.
-/

set_option warningAsError true

namespace DirectedCounting

open scoped BigOperators

/-- Fiber sums compose: summing leaf masses first at the middle level and
then at the old level is the same as summing them directly through the
composite parent map. -/
theorem fiberMass_comp
    {Old Middle Leaf : Type*}
    [Fintype Middle] [Fintype Leaf]
    [DecidableEq Old] [DecidableEq Middle]
    (parent : Middle → Old) (child : Leaf → Middle)
    (mass : Leaf → ℕ) (i : Old) :
    fiberMass parent (fun j ↦ fiberMass child mass j) i =
      fiberMass (parent ∘ child) mass i := by
  classical
  unfold fiberMass refinementFiber
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext l
    simp [Function.comp_apply]
  · intro l _hl
    rfl

namespace CanonicalFiberCompletion

variable {anchorCount leafCount : Nat}

/-- The least terminal descendant is a deterministic representative of a
nonempty anchor fiber. -/
def canonicalLeaf
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (a : Fin anchorCount) : Fin leafCount :=
  (refinementFiber ancestor a).min' (by
    obtain ⟨l, hl⟩ := covered a
    exact ⟨l, by simp [refinementFiber, hl]⟩)

theorem canonicalLeaf_mem
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (a : Fin anchorCount) :
    canonicalLeaf ancestor covered a ∈ refinementFiber ancestor a := by
  exact Finset.min'_mem _ _

theorem ancestor_canonicalLeaf
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (a : Fin anchorCount) :
    ancestor (canonicalLeaf ancestor covered a) = a := by
  simpa [refinementFiber] using canonicalLeaf_mem ancestor covered a

/-- Give every terminal leaf one unit and put the unused anchor mass on the
least leaf in the same anchor fiber. -/
def terminalWeight
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (anchorWeight : Fin anchorCount → Nat)
    (l : Fin leafCount) : Nat :=
  1 + if l = canonicalLeaf ancestor covered (ancestor l) then
    anchorWeight (ancestor l) - (refinementFiber ancestor (ancestor l)).card
  else 0

theorem terminalWeight_pos
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (anchorWeight : Fin anchorCount → Nat)
    (l : Fin leafCount) :
    0 < terminalWeight ancestor covered anchorWeight l := by
  unfold terminalWeight
  omega

/-- The canonical assignment sums to the proposed anchor vector whenever
each coordinate has enough mass for all of its terminal descendants. -/
theorem fiberMass_terminalWeight
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (anchorWeight : Fin anchorCount → Nat)
    (capacity : ∀ a,
      (refinementFiber ancestor a).card ≤ anchorWeight a)
    (a : Fin anchorCount) :
    fiberMass ancestor
        (terminalWeight ancestor covered anchorWeight) a =
      anchorWeight a := by
  classical
  let F := refinementFiber ancestor a
  let c := canonicalLeaf ancestor covered a
  have hcF : c ∈ F := by
    exact canonicalLeaf_mem ancestor covered a
  have hcapacity : F.card ≤ anchorWeight a := capacity a
  unfold fiberMass
  change (∑ l ∈ F, terminalWeight ancestor covered anchorWeight l) =
    anchorWeight a
  calc
    (∑ l ∈ F, terminalWeight ancestor covered anchorWeight l) =
        ∑ l ∈ F,
          (1 + if l = c then anchorWeight a - F.card else 0) := by
            apply Finset.sum_congr rfl
            intro l hl
            have hal : ancestor l = a := by
              simpa [F, refinementFiber] using hl
            simp only [terminalWeight, hal]
            rfl
    _ = F.card + (anchorWeight a - F.card) := by
      rw [Finset.sum_add_distrib]
      simp [hcF]
    _ = anchorWeight a := by omega

/-- Positivity alone forces the terminal-descendant capacity inequality. -/
theorem capacity_of_positive_conservation
    (ancestor : Fin leafCount → Fin anchorCount)
    (anchorWeight : Fin anchorCount → Nat)
    (leafWeight : Fin leafCount → Nat)
    (positive : ∀ l, 0 < leafWeight l)
    (conserve : ∀ a, fiberMass ancestor leafWeight a = anchorWeight a)
    (a : Fin anchorCount) :
    (refinementFiber ancestor a).card ≤ anchorWeight a := by
  let F := refinementFiber ancestor a
  have hpoint : ∀ l ∈ F, 1 ≤ leafWeight l := by
    intro l _hl
    exact Nat.succ_le_iff.mpr (positive l)
  calc
    F.card = ∑ _l ∈ F, 1 := by simp
    _ ≤ ∑ l ∈ F, leafWeight l :=
      Finset.sum_le_sum hpoint
    _ = fiberMass ancestor leafWeight a := by
      rfl
    _ = anchorWeight a := conserve a

/-- Exact characterization of feasible positive integral leaf weights.  The
right-to-left implication is witnessed by `terminalWeight`, hence involves
no search over integer profiles. -/
theorem exists_positive_conservation_iff
    (ancestor : Fin leafCount → Fin anchorCount)
    (covered : Function.Surjective ancestor)
    (anchorWeight : Fin anchorCount → Nat) :
    (∃ leafWeight : Fin leafCount → Nat,
        (∀ l, 0 < leafWeight l) ∧
        ∀ a, fiberMass ancestor leafWeight a = anchorWeight a) ↔
      ∀ a, (refinementFiber ancestor a).card ≤ anchorWeight a := by
  constructor
  · rintro ⟨leafWeight, positive, conserve⟩ a
    exact capacity_of_positive_conservation ancestor anchorWeight leafWeight
      positive conserve a
  · intro capacity
    exact ⟨terminalWeight ancestor covered anchorWeight,
      terminalWeight_pos ancestor covered anchorWeight,
      fiberMass_terminalWeight ancestor covered anchorWeight capacity⟩

end CanonicalFiberCompletion

/-!
## A checkable output of the exact anchor solver

The construction below does not postulate a Perron--Frobenius solver.  It
accepts a proposed integral vector and verifies every equation by bounded
computation.  A future fraction-free kernel routine can produce this output;
soundness will continue to depend only on `check = true`.
-/

/-- The square matrix and diagonal data exposed at a nonbranching anchor. -/
structure IntegralAnchorInstance (q : Nat) where
  degree : Fin q → Nat
  multiplicity : Fin q → Fin q → Nat
  leader : Fin q

namespace IntegralAnchorInstance

variable {q : Nat} (A : IntegralAnchorInstance q)

def support (i j : Fin q) : Bool := decide (0 < A.multiplicity i j)

/-- A solver output contains data only.  All claimed properties are checked
separately by `check`. -/
structure Output (q candidate : Nat) where
  weight : Fin q → Nat

variable {candidate : Nat} (output : Output q candidate)

structure Valid : Prop where
  degree_pos : ∀ i, 0 < A.degree i
  support_strongly_connected : strongConnectivityCheck A.support = true
  weight_pos : ∀ i, 0 < output.weight i
  total : (∑ i, output.weight i) = candidate
  leader_weight : output.weight A.leader = 1
  balance : ∀ i,
    (∑ j, A.multiplicity i j * output.weight j) =
      A.degree i * output.weight i

def validRaw : Prop :=
  (∀ i, 0 < A.degree i) ∧
  strongConnectivityCheck A.support = true ∧
  (∀ i, 0 < output.weight i) ∧
  (∑ i, output.weight i) = candidate ∧
  output.weight A.leader = 1 ∧
  ∀ i, (∑ j, A.multiplicity i j * output.weight j) =
    A.degree i * output.weight i

instance : Decidable (A.validRaw output) := by
  unfold validRaw
  infer_instance

theorem validRaw_iff : A.validRaw output ↔ A.Valid output := by
  constructor
  · rintro ⟨hdegree, hsc, hpositive, htotal, hleader, hbalance⟩
    exact ⟨hdegree, hsc, hpositive, htotal, hleader, hbalance⟩
  · intro h
    exact ⟨h.degree_pos, h.support_strongly_connected, h.weight_pos,
      h.total, h.leader_weight, h.balance⟩

/-- Exact bounded verifier for an anchor-solver output. -/
def check : Bool := decide (A.validRaw output)

theorem check_eq_true_iff : A.check output = true ↔ A.Valid output := by
  rw [check, decide_eq_true_eq, A.validRaw_iff]

end IntegralAnchorInstance

/-!
## A whole trailing refinement suffix

`terminalAncestor h` is redundant, locally checkable data: it is obtained by
composing the black-parent maps from the terminal frontier back to level `h`.
Keeping it explicit makes both the checker and the proof simple.  The
`terminal_step` equations verify every composition, so no semantic fact is
hidden in this representation.
-/

/-- A finite suffix starting at its last nonbranching anchor (level zero)
and ending at level `R`.  Every transition is branching.  Surjectivity says
that no represented class disappears before the terminal frontier. -/
structure TrailingBranchSuffix (R : Nat) where
  classCount : Nat → Nat
  parent : (h : Nat) → Fin (classCount (h + 1)) → Fin (classCount h)
  terminalAncestor : (h : Nat) →
    Fin (classCount R) → Fin (classCount h)
  terminal_identity : terminalAncestor R = id
  terminal_step : ∀ h, h < R → ∀ l,
    parent h (terminalAncestor (h + 1) l) = terminalAncestor h l
  terminal_covered : ∀ h, h ≤ R →
    Function.Surjective (terminalAncestor h)
  all_branching : ∀ h, h < R → classCount h < classCount (h + 1)

namespace TrailingBranchSuffix

variable {R : Nat} (S : TrailingBranchSuffix R)

/-- The terminal leaves below one node at level `h`. -/
def terminalFiber (h : Nat) (i : Fin (S.classCount h)) :
    Finset (Fin (S.classCount R)) :=
  refinementFiber (S.terminalAncestor h) i

/-- The capacity test needed at the last nonbranching anchor. -/
def AnchorCapacity (anchorWeight : Fin (S.classCount 0) → Nat) : Prop :=
  ∀ i, (S.terminalFiber 0 i).card ≤ anchorWeight i

instance (anchorWeight : Fin (S.classCount 0) → Nat) :
    Decidable (S.AnchorCapacity anchorWeight) := by
  unfold AnchorCapacity terminalFiber
  infer_instance

/-- Boolean form of the per-anchor capacity test. -/
def anchorCapacityCheck
    (anchorWeight : Fin (S.classCount 0) → Nat) : Bool :=
  decide (S.AnchorCapacity anchorWeight)

theorem anchorCapacityCheck_eq_true_iff
    (anchorWeight : Fin (S.classCount 0) → Nat) :
    S.anchorCapacityCheck anchorWeight = true ↔
      S.AnchorCapacity anchorWeight := by
  simp [anchorCapacityCheck]

theorem anchorCovered : Function.Surjective (S.terminalAncestor 0) :=
  S.terminal_covered 0 (Nat.zero_le R)

/-- Canonical positive masses on the terminal frontier. -/
def canonicalTerminalWeight
    (anchorWeight : Fin (S.classCount 0) → Nat) :
    Fin (S.classCount R) → Nat :=
  CanonicalFiberCompletion.terminalWeight
    (S.terminalAncestor 0) S.anchorCovered anchorWeight

/-- Backward propagation is just a sum over terminal descendants. -/
def backwardWeight
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (h : Nat) (i : Fin (S.classCount h)) : Nat :=
  fiberMass (S.terminalAncestor h) (S.canonicalTerminalWeight anchorWeight) i

theorem canonicalTerminalWeight_pos
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (l : Fin (S.classCount R)) :
    0 < S.canonicalTerminalWeight anchorWeight l := by
  exact CanonicalFiberCompletion.terminalWeight_pos
    (S.terminalAncestor 0) S.anchorCovered anchorWeight l

/-- The propagated vector agrees exactly with the checked anchor vector. -/
theorem backwardWeight_zero
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (capacity : S.AnchorCapacity anchorWeight)
    (i : Fin (S.classCount 0)) :
    S.backwardWeight anchorWeight 0 i = anchorWeight i := by
  exact CanonicalFiberCompletion.fiberMass_terminalWeight
    (S.terminalAncestor 0) S.anchorCovered anchorWeight capacity i

/-- At the endpoint, descendant summation reduces to the canonical terminal
vector itself. -/
theorem backwardWeight_terminal
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (l : Fin (S.classCount R)) :
    S.backwardWeight anchorWeight R l =
      S.canonicalTerminalWeight anchorWeight l := by
  unfold backwardWeight
  rw [S.terminal_identity]
  have hfiber :
      refinementFiber (id : Fin (S.classCount R) → Fin (S.classCount R)) l =
        {l} := by
    ext x
    simp [refinementFiber]
  rw [fiberMass, hfiber]
  simp

/-- Every represented intermediate class receives positive mass. -/
theorem backwardWeight_pos
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (h : Nat) (hh : h ≤ R) (i : Fin (S.classCount h)) :
    0 < S.backwardWeight anchorWeight h i := by
  obtain ⟨l, hl⟩ := S.terminal_covered h hh i
  unfold backwardWeight fiberMass
  apply Finset.sum_pos'
  · exact fun _l _hl ↦ Nat.zero_le _
  · refine ⟨l, ?_, S.canonicalTerminalWeight_pos anchorWeight l⟩
    simp [refinementFiber, hl]

/-- Backward descendant sums exactly conserve mass through every black-parent
transition. -/
theorem backwardWeight_conserve
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (h : Nat) (hh : h < R) (i : Fin (S.classCount h)) :
    fiberMass (S.parent h) (S.backwardWeight anchorWeight (h + 1)) i =
      S.backwardWeight anchorWeight h i := by
  unfold backwardWeight
  rw [fiberMass_comp]
  unfold fiberMass refinementFiber
  apply Finset.sum_congr
  · ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply]
    rw [S.terminal_step h hh l]
  · intro l _hl
    rfl

/-- Terminal coverage and the checked composition equations imply coverage
of every immediate black-parent map. -/
theorem parent_surjective
    (h : Nat) (hh : h < R) : Function.Surjective (S.parent h) := by
  intro i
  obtain ⟨l, hl⟩ := S.terminal_covered h (Nat.le_of_lt hh) i
  refine ⟨S.terminalAncestor (h + 1) l, ?_⟩
  rw [S.terminal_step h hh l, hl]

/-- Consequently every intermediate vector has the same total mass as the
anchor vector. -/
theorem backwardWeight_total
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (capacity : S.AnchorCapacity anchorWeight)
    (h : Nat) (hh : h ≤ R) :
    (∑ i : Fin (S.classCount h), S.backwardWeight anchorWeight h i) =
      ∑ i : Fin (S.classCount 0), anchorWeight i := by
  calc
    (∑ i : Fin (S.classCount h), S.backwardWeight anchorWeight h i) =
        ∑ l : Fin (S.classCount R), S.canonicalTerminalWeight anchorWeight l := by
      let step : RefinementData (Fin (S.classCount h))
          (Fin (S.classCount R)) :=
        { parent := S.terminalAncestor h
          yOld := S.backwardWeight anchorWeight h
          zOld := S.backwardWeight anchorWeight h
          yNew := S.canonicalTerminalWeight anchorWeight
          zNew := S.canonicalTerminalWeight anchorWeight
          yOld_pos := S.backwardWeight_pos anchorWeight h hh
          zOld_pos := S.backwardWeight_pos anchorWeight h hh
          yNew_pos := S.canonicalTerminalWeight_pos anchorWeight
          zNew_pos := S.canonicalTerminalWeight_pos anchorWeight
          y_conserve := fun i ↦ rfl
          z_subconserve := fun i ↦ Nat.le_refl _ }
      exact step.referenceMass_eq.symm
    _ = ∑ i : Fin (S.classCount 0), S.backwardWeight anchorWeight 0 i := by
      let step : RefinementData (Fin (S.classCount 0))
          (Fin (S.classCount R)) :=
        { parent := S.terminalAncestor 0
          yOld := S.backwardWeight anchorWeight 0
          zOld := S.backwardWeight anchorWeight 0
          yNew := S.canonicalTerminalWeight anchorWeight
          zNew := S.canonicalTerminalWeight anchorWeight
          yOld_pos := S.backwardWeight_pos anchorWeight 0 (Nat.zero_le R)
          zOld_pos := S.backwardWeight_pos anchorWeight 0 (Nat.zero_le R)
          yNew_pos := S.canonicalTerminalWeight_pos anchorWeight
          zNew_pos := S.canonicalTerminalWeight_pos anchorWeight
          y_conserve := fun i ↦ rfl
          z_subconserve := fun i ↦ Nat.le_refl _ }
      exact step.referenceMass_eq
    _ = ∑ i : Fin (S.classCount 0), anchorWeight i := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact S.backwardWeight_zero anchorWeight capacity i

/-- Feasibility of a positive terminal completion is exactly the executable
capacity test. -/
theorem exists_terminal_completion_iff
    (anchorWeight : Fin (S.classCount 0) → Nat) :
    (∃ terminalWeight : Fin (S.classCount R) → Nat,
        (∀ l, 0 < terminalWeight l) ∧
        ∀ i, fiberMass (S.terminalAncestor 0) terminalWeight i =
          anchorWeight i) ↔
      S.AnchorCapacity anchorWeight := by
  exact CanonicalFiberCompletion.exists_positive_conservation_iff
    (S.terminalAncestor 0) S.anchorCovered anchorWeight

/-! ### Combined exact-anchor and suffix recognizer -/

/-- The complete bounded test after a solver proposes an anchor vector. -/
def lastAnchorCompletionCheck
    (A : IntegralAnchorInstance (S.classCount 0))
    (output : IntegralAnchorInstance.Output (S.classCount 0) candidate) :
    Bool :=
  A.check output && S.anchorCapacityCheck output.weight

theorem lastAnchorCompletionCheck_eq_true_iff
    (A : IntegralAnchorInstance (S.classCount 0))
    (output : IntegralAnchorInstance.Output (S.classCount 0) candidate) :
    S.lastAnchorCompletionCheck A output = true ↔
      A.Valid output ∧ S.AnchorCapacity output.weight := by
  simp [lastAnchorCompletionCheck,
    IntegralAnchorInstance.check_eq_true_iff,
    S.anchorCapacityCheck_eq_true_iff]

/-- An accepted combined check produces positive, exactly conserving suffix
weights of the claimed total mass. -/
theorem accepted_completion_properties
    (A : IntegralAnchorInstance (S.classCount 0))
    (output : IntegralAnchorInstance.Output (S.classCount 0) candidate)
    (accepted : S.lastAnchorCompletionCheck A output = true) :
    (∀ h, h ≤ R → ∀ i,
      0 < S.backwardWeight output.weight h i) ∧
    (∀ h, h < R → ∀ i,
      fiberMass (S.parent h) (S.backwardWeight output.weight (h + 1)) i =
        S.backwardWeight output.weight h i) ∧
    (∀ i, S.backwardWeight output.weight 0 i = output.weight i) ∧
    (∑ i, S.backwardWeight output.weight 0 i) = candidate := by
  have recognized := (S.lastAnchorCompletionCheck_eq_true_iff A output).mp
    accepted
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hh i
    exact S.backwardWeight_pos output.weight h hh i
  · intro h hh i
    exact S.backwardWeight_conserve output.weight h hh i
  · intro i
    exact S.backwardWeight_zero output.weight recognized.2 i
  · calc
      (∑ i, S.backwardWeight output.weight 0 i) =
          ∑ i, output.weight i := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact S.backwardWeight_zero output.weight recognized.2 i
      _ = candidate := recognized.1.total

/-! ### Packaging for the existing finite prefix witness -/

/-- Install the canonical suffix weights in the finite witness type used by
`BranchAwarePrefixCheck`.  Degree, red, and leader data are copied from the
visible DAG; no candidate profile is enumerated. -/
def toBranchAwarePrefixWitness
    (candidate : Nat)
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (degree : (h : Nat) → Fin (S.classCount (h + 1)) → Nat)
    (redMultiplicity : (h : Nat) →
      Fin (S.classCount h) → Fin (S.classCount (h + 1)) → Nat)
    (leader : (h : Nat) → Fin (S.classCount h)) :
    BranchAwarePrefixWitness candidate R where
  classCount := S.classCount
  parent := S.parent
  degree := degree
  redMultiplicity := redMultiplicity
  leader := leader
  weight := S.backwardWeight anchorWeight

theorem toBranchAwarePrefixWitness_weight_pos
    (candidate : Nat)
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (degree : (h : Nat) → Fin (S.classCount (h + 1)) → Nat)
    (redMultiplicity : (h : Nat) →
      Fin (S.classCount h) → Fin (S.classCount (h + 1)) → Nat)
    (leader : (h : Nat) → Fin (S.classCount h))
    (h : Nat) (hh : h ≤ R) (i : Fin (S.classCount h)) :
    0 < (S.toBranchAwarePrefixWitness candidate anchorWeight degree
      redMultiplicity leader).weight h i := by
  exact S.backwardWeight_pos anchorWeight h hh i

theorem toBranchAwarePrefixWitness_blackConservesAt
    (candidate : Nat)
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (degree : (h : Nat) → Fin (S.classCount (h + 1)) → Nat)
    (redMultiplicity : (h : Nat) →
      Fin (S.classCount h) → Fin (S.classCount (h + 1)) → Nat)
    (leader : (h : Nat) → Fin (S.classCount h))
    (h : Nat) (hh : h < R) :
    (S.toBranchAwarePrefixWitness candidate anchorWeight degree
      redMultiplicity leader).blackConservesAt h := by
  intro i
  rw [(S.toBranchAwarePrefixWitness candidate anchorWeight degree
    redMultiplicity leader).blackFiberMass_eq_fiberMass]
  exact S.backwardWeight_conserve anchorWeight h hh i

theorem toBranchAwarePrefixWitness_parentSurjectiveAt
    (candidate : Nat)
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (degree : (h : Nat) → Fin (S.classCount (h + 1)) → Nat)
    (redMultiplicity : (h : Nat) →
      Fin (S.classCount h) → Fin (S.classCount (h + 1)) → Nat)
    (leader : (h : Nat) → Fin (S.classCount h))
    (h : Nat) (hh : h < R) :
    (S.toBranchAwarePrefixWitness candidate anchorWeight degree
      redMultiplicity leader).parentSurjectiveAt h := by
  exact S.parent_surjective h hh

theorem toBranchAwarePrefixWitness_branchingAt
    (candidate : Nat)
    (anchorWeight : Fin (S.classCount 0) → Nat)
    (degree : (h : Nat) → Fin (S.classCount (h + 1)) → Nat)
    (redMultiplicity : (h : Nat) →
      Fin (S.classCount h) → Fin (S.classCount (h + 1)) → Nat)
    (leader : (h : Nat) → Fin (S.classCount h))
    (h : Nat) (hh : h < R) :
    (S.toBranchAwarePrefixWitness candidate anchorWeight degree
      redMultiplicity leader).branchingAt h := by
  exact S.all_branching h hh

end TrailingBranchSuffix

end DirectedCounting
