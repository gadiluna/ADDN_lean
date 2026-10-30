import Counting.CoreHistory

/-!
# Credit lemmas for concrete multigraph history trees

These wrappers instantiate all three credit lemmas of the paper on actual
history-quotient fibers. Only the candidate checks from Steps 1--4 enter
the prefix theorem; no suffix check or Step 5 premise is used.
-/

namespace Counting.CreditHistory

open DirectedCounting DirectedCounting.PaperHistory

variable {V : Type*} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- Credit under refinement for the actual children of an actual history node. -/
theorem credit_under_refinement (r : ℕ)
    (visible : Finset (Node G leader (r + 1)))
    (candidate : Node G leader (r + 1) → ℕ) (oldCandidate : Node G leader r → ℕ)
    (u : Node G leader r)
    (children : (visible.filter (fun i => parent G leader r i = u)).Nonempty)
    (backward : (∑ i ∈ visible.filter (fun i => parent G leader r i = u), candidate i) = oldCandidate u) :
    (∑ i ∈ visible.filter (fun i => parent G leader r i = u),
      credit (anonymity G leader (r + 1) i) (candidate i)) ≤
      credit (anonymity G leader r u) (oldCandidate u) :=
  Counting.credit_under_refinement _ (anonymity G leader (r + 1)) candidate _ _ children
    (fun i _ => anonymity_pos G leader (r + 1) i) (children_mass_le G leader r visible u) backward

/-- The equality clause preserves the actual set of agents, not just its size. -/
theorem credit_refinement_rigidity (r : ℕ)
    (visible : Finset (Node G leader (r + 1)))
    (candidate : Node G leader (r + 1) → ℕ) (oldCandidate : Node G leader r → ℕ)
    (u : Node G leader r)
    (backward : (∑ i ∈ visible.filter (fun i => parent G leader r i = u), candidate i) = oldCandidate u)
    (preserved : (∑ i ∈ visible.filter (fun i => parent G leader r i = u),
      credit (anonymity G leader (r + 1) i) (candidate i)) =
      credit (anonymity G leader r u) (oldCandidate u))
    (j : Node G leader (r + 1)) (hj : j ∈ visible) (hparent : parent G leader r j = u)
    (saturated : anonymity G leader (r + 1) j ≤ candidate j) :
    visible.filter (fun i => parent G leader r i = u) = {j} ∧
      fiber G leader (r + 1) j = fiber G leader r u ∧ candidate j = oldCandidate u := by
  classical
  obtain ⟨hchild, hactual, hcandidate⟩ := Counting.credit_refinement_rigidity
    (visible.filter (fun i => parent G leader r i = u)) (anonymity G leader (r + 1)) candidate _ _
    (fun i _ => anonymity_pos G leader (r + 1) i) (children_mass_le G leader r visible u)
    backward preserved j (Finset.mem_filter.mpr ⟨hj, hparent⟩) saturated
  refine ⟨hchild, ?_, hcandidate⟩
  apply Finset.eq_of_subset_of_card_le
  · simpa only [hparent] using fiber_subset_parent G leader r j
  · exact hactual.ge

/-- Equality of the two unions of concrete fibers implies that every actual
child of a minimum-node parent is itself a minimum node. -/
theorem parent_closed_of_equal_fiber_unions [DecidableEq V] (r : ℕ)
    (nodes : Finset (Node G leader (r + 1)))
    (equalFibers : ((nodes.image (parent G leader r)).biUnion (fiber G leader r)) =
      nodes.biUnion (fiber G leader (r + 1))) :
    ∀ i, parent G leader r i ∈ nodes.image (parent G leader r) → i ∈ nodes := by
  classical
  intro i hiparent
  have hout : i.out ∈ fiber G leader (r + 1) i := by simp
  have hin : i.out ∈ (nodes.image (parent G leader r)).biUnion (fiber G leader r) :=
    Finset.mem_biUnion.mpr ⟨parent G leader r i, hiparent, fiber_subset_parent G leader r i hout⟩
  rw [equalFibers] at hin
  obtain ⟨j, hj, hji⟩ := Finset.mem_biUnion.mp hin
  have hij : i = j := by simpa only [mem_fiber, classOf_out] using hji
  simpa only [hij] using hj

noncomputable def minimumNodes (r : ℕ) (visible : Finset (Node G leader (r + 1)))
    (candidate : Node G leader (r + 1) → ℕ) (alpha : ℚ) : Finset (Node G leader (r + 1)) :=
  visible.filter (fun i => (anonymity G leader (r + 1) i : ℚ) / candidate i = alpha)

/-- The paper's minimum-ratio closure lemma with exactly its fiber-union
premise. Actual flow and connected quotient support come from the network. -/
theorem minimum_ratio_closure [DecidableEq V] (r : ℕ)
    (visible : Finset (Node G leader (r + 1)))
    (candidate : Node G leader (r + 1) → ℕ) (alpha : ℚ)
    (positive : ∀ i ∈ visible, 0 < candidate i)
    (minimum : ∀ i ∈ visible, alpha ≤ (anonymity G leader (r + 1) i : ℚ) / candidate i)
    (attained : (minimumNodes G leader r visible candidate alpha).Nonempty)
    (candidateFlow : ∀ u ∈ visible.image (parent G leader r),
      (∑ i ∈ visible, if parent G leader r i = u then outdegreeLabel G leader r i * candidate i else 0) =
      ∑ i ∈ visible, redMultiplicity G leader r u i * candidate i)
    (equalFibers :
      (((minimumNodes G leader r visible candidate alpha).image (parent G leader r)).biUnion
        (fiber G leader r)) =
      (minimumNodes G leader r visible candidate alpha).biUnion (fiber G leader (r + 1)))
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v)) :
    visible = Finset.univ ∧
      ∀ i, (anonymity G leader (r + 1) i : ℚ) / candidate i = alpha := by
  have hnodes : minimumNodes G leader r visible candidate alpha =
      visible.filter (fun i => (anonymity G leader (r + 1) i : ℚ) = alpha * candidate i) := by
    ext i
    simp only [minimumNodes, Finset.mem_filter]
    by_cases hi : i ∈ visible
    · simp only [hi, true_and]
      exact div_eq_iff (by exact_mod_cast Nat.ne_of_gt (positive i hi))
    · simp only [hi, false_and]
  have hclosed := parent_closed_of_equal_fiber_unions G leader r _ equalFibers
  rw [hnodes] at hclosed attained
  have actualFlow : ∀ u,
      (∑ i, if parent G leader r i = u then
        (outdegreeLabel G leader r i : ℚ) * anonymity G leader (r + 1) i else 0) =
      ∑ i, (redMultiplicity G leader r u i : ℚ) * anonymity G leader (r + 1) i := by
    intro u
    have hn := (flow_balance G leader r u).symm
    rw [Finset.sum_filter] at hn
    exact_mod_cast hn
  have candidateFlowQ : ∀ u ∈ visible.image (parent G leader r),
      (∑ i ∈ visible, if parent G leader r i = u then
        (outdegreeLabel G leader r i : ℚ) * candidate i else 0) =
      ∑ i ∈ visible, (redMultiplicity G leader r u i : ℚ) * candidate i := by
    intro u hu
    exact_mod_cast candidateFlow u hu
  have connectedQ : ∀ i j, Relation.ReflTransGen
      (fun p q => (0 : ℚ) < redMultiplicity G leader r (parent G leader r p) q) i j := by
    simpa only [Nat.cast_pos, FlatHistory.weight, StronglyConnected] using
      FlatHistory.weight_stronglyConnected G leader r connected
  obtain ⟨hfull, hratio⟩ := MinimumRatio.minimum_ratio_closure (parent G leader r) visible
    (fun i => (anonymity G leader (r + 1) i : ℚ)) (fun i => (candidate i : ℚ))
    (fun i => (outdegreeLabel G leader r i : ℚ)) (fun u i => (redMultiplicity G leader r u i : ℚ))
    alpha (fun i => by exact_mod_cast anonymity_pos G leader (r + 1) i) (fun _ _ => Nat.cast_nonneg _)
    (fun i hi => (le_div_iff₀ (by exact_mod_cast positive i hi)).mp (minimum i hi))
    actualFlow candidateFlowQ hclosed attained connectedQ
  refine ⟨hfull, fun i => ?_⟩
  apply (div_eq_iff (show (candidate i : ℚ) ≠ 0 from by
    exact_mod_cast Nat.ne_of_gt (positive i (hfull ▸ Finset.mem_univ i)))).mpr
  exact hratio i

/-- Credit loss for one concrete transition. Its premises contain only
the local checks inherited from Steps 1--4, with no suffix premise. -/
theorem credit_loss (r m : ℕ)
    (previous : Finset (Node G leader r)) (visible : Finset (Node G leader (r + 1)))
    (oldCandidate : Node G leader r → ℕ) (candidate : Node G leader (r + 1) → ℕ)
    (positive : ∀ i ∈ visible, 0 < candidate i)
    (parentVisible : ∀ i ∈ visible, parent G leader r i ∈ previous)
    (children : ∀ u ∈ previous, (visible.filter (fun i => parent G leader r i = u)).Nonempty)
    (backward : ∀ u ∈ previous,
      (∑ i ∈ visible.filter (fun i => parent G leader r i = u), candidate i) = oldCandidate u)
    (candidateFlow : ∀ u ∈ previous,
      (∑ i ∈ visible, if parent G leader r i = u then outdegreeLabel G leader r i * candidate i else 0) =
      ∑ i ∈ visible, redMultiplicity G leader r u i * candidate i)
    (leaderPositive : 0 < FlatHistory.leaderCount leader)
    (leaderCandidate :
      (∑ i ∈ visible ∩ Finset.univ.filter (fun c => label G leader (r + 1) c = true), candidate i) =
      FlatHistory.leaderCount leader)
    (candidateTotal : (∑ i ∈ visible, candidate i) = m)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v)) :
    (∑ i ∈ visible, credit (anonymity G leader (r + 1) i) (candidate i)) ≤
      (∑ u ∈ previous, credit (anonymity G leader r u) (oldCandidate u)) ∧
    ((∑ i ∈ visible, credit (anonymity G leader (r + 1) i) (candidate i)) =
      (∑ u ∈ previous, credit (anonymity G leader r u) (oldCandidate u)) →
      visible = Finset.univ ∧ candidate = anonymity G leader (r + 1) ∧ m = Fintype.card V) := by
  constructor
  · calc
      (∑ i ∈ visible, credit (anonymity G leader (r + 1) i) (candidate i)) =
          ∑ u ∈ previous, ∑ i ∈ visible.filter (fun i => parent G leader r i = u),
            credit (anonymity G leader (r + 1) i) (candidate i) :=
        (Finset.sum_fiberwise_of_maps_to parentVisible _).symm
      _ ≤ ∑ u ∈ previous, credit (anonymity G leader r u) (oldCandidate u) :=
        Finset.sum_le_sum fun u hu => credit_under_refinement G leader r visible candidate oldCandidate u
          (children u hu) (backward u hu)
  · intro heq
    have hpartition : ∀ u,
        (∑ i ∈ Finset.univ.filter (fun i => parent G leader r i = u), anonymity G leader (r + 1) i) =
          anonymity G leader r u := fun u =>
      (children_mass_eq_iff G leader r Finset.univ u).mpr (fun i _ => Finset.mem_univ i)
    have hflow : ∀ u,
        (∑ i, if parent G leader r i = u then outdegreeLabel G leader r i * anonymity G leader (r + 1) i else 0) =
          ∑ i, redMultiplicity G leader r u i * anonymity G leader (r + 1) i := by
      intro u
      simpa only [Finset.sum_filter] using (flow_balance G leader r u).symm
    obtain ⟨hfull, hvalues⟩ := Counting.credit_preserved_identifies_population (parent G leader r)
      visible previous (anonymity G leader (r + 1)) candidate (outdegreeLabel G leader r)
      (redMultiplicity G leader r) (anonymity G leader r) oldCandidate
      (Finset.univ.filter (fun c => label G leader (r + 1) c = true)) (FlatHistory.leaderCount leader)
      (anonymity_pos G leader (r + 1)) positive parentVisible children hpartition backward hflow candidateFlow
      (FlatHistory.weight_stronglyConnected G leader r connected) (label_mass_eq G leader (r + 1) true)
      leaderCandidate leaderPositive heq
    refine ⟨hfull, hvalues.symm, ?_⟩
    calc
      m = ∑ i ∈ visible, candidate i := candidateTotal.symm
      _ = ∑ i, anonymity G leader (r + 1) i := by rw [hfull, ← hvalues]
      _ = Fintype.card V := total_anonymity G leader (r + 1)

/-- Exactly the prefix information used by the paper's three credit
lemmas. The structure contains no final suffix, descendant audit, or Step 5. -/
structure PrefixChecks (m h : ℕ)
    (visible : ∀ r, Finset (Node G leader r))
    (candidate : ∀ r, Node G leader r → ℕ) where
  leader_positive : 0 < FlatHistory.leaderCount leader
  anchor_candidate_positive : ∀ i ∈ visible h, 0 < candidate h i
  anchor_leader_candidate :
    (∑ i ∈ visible h ∩ Finset.univ.filter (fun c => label G leader h c = true), candidate h i) =
      FlatHistory.leaderCount leader
  anchor_total : (∑ i ∈ visible h, candidate h i) = m
  parent_visible : ∀ r, r < h → ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r
  children_nonempty : ∀ r, r < h → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty
  backward : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
      candidate r u
  candidate_flow : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1),
      if parent G leader r i = u then outdegreeLabel G leader r i * candidate (r + 1) i else 0) =
    ∑ i ∈ visible (r + 1), redMultiplicity G leader r u i * candidate (r + 1) i

namespace PrefixChecks

variable {G leader} {m h : ℕ}
  {visible : ∀ r, Finset (Node G leader r)} {candidate : ∀ r, Node G leader r → ℕ}
  (C : PrefixChecks G leader m h visible candidate)

include C in
theorem candidate_total (r : ℕ) (hr : r ≤ h) : (∑ i ∈ visible r, candidate r i) = m := by
  apply Nat.decreasingInduction (motive := fun r _ => (∑ i ∈ visible r, candidate r i) = m)
    ?_ C.anchor_total hr
  intro k hk ih
  calc
    (∑ u ∈ visible k, candidate k u) =
        ∑ u ∈ visible k, ∑ i ∈ (visible (k + 1)).filter (fun i => parent G leader k i = u),
          candidate (k + 1) i := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (C.backward k hk u hu).symm
    _ = ∑ i ∈ visible (k + 1), candidate (k + 1) i :=
      Finset.sum_fiberwise_of_maps_to (C.parent_visible k hk) _
    _ = m := ih

include C in
/-- The complete paper Credit loss lemma on a concrete prefix that passed
Steps 1--4: total credit is nonincreasing, and any equality identifies the
population. Positivity, leader normalization and candidate totals at the
transition are derived from the anchor, not assumed locally. -/
theorem credit_loss (r : ℕ) (hr : r < h)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v)) :
    (∑ i ∈ visible (r + 1), credit (anonymity G leader (r + 1) i) (candidate (r + 1) i)) ≤
      (∑ u ∈ visible r, credit (anonymity G leader r u) (candidate r u)) ∧
    ((∑ i ∈ visible (r + 1), credit (anonymity G leader (r + 1) i) (candidate (r + 1) i)) =
      (∑ u ∈ visible r, credit (anonymity G leader r u) (candidate r u)) →
      visible (r + 1) = Finset.univ ∧ candidate (r + 1) = anonymity G leader (r + 1) ∧
        m = Fintype.card V) := by
  have hpositive := CoreHistory.candidate_positive_of_anchor G leader h visible candidate
    C.anchor_candidate_positive C.children_nonempty C.backward
  have hleaders := CoreHistory.leader_candidate_of_anchor G leader h (FlatHistory.leaderCount leader)
    visible candidate C.anchor_leader_candidate C.parent_visible C.backward
  exact CreditHistory.credit_loss G leader r m (visible r) (visible (r + 1))
    (candidate r) (candidate (r + 1)) (hpositive (r + 1) (by omega))
    (C.parent_visible r hr) (C.children_nonempty r hr) (C.backward r hr) (C.candidate_flow r hr)
    C.leader_positive (hleaders (r + 1) (by omega)) (C.candidate_total (r + 1) (by omega)) connected

end PrefixChecks

end Counting.CreditHistory
