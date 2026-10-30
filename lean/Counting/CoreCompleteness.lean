import Counting.CoreHistory

/-!
# Completeness of the mathematical core certificate

Every exhaustive prefix through level `n` of a nonempty population has a
last flat transition. Actual anonymities supply a positive, normalized
solution of every prefix audit and pass the descendant-count suffix test.
These mathematical certificate results support the executable DAG/solver
correspondence proved in ExecutableRefinementComplete and its extensions.
-/

namespace Counting.CoreCompleteness

open DirectedCounting DirectedCounting.PaperHistory

variable {V : Type*} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

theorem flat_iff_child_card_one (r : ℕ) :
    FlatHistory.Flat G leader r ↔ ∀ u : Node G leader r,
      (Finset.univ.filter (fun i => parent G leader r i = u)).card = 1 := by
  rw [FlatHistory.flat_iff_unique_child]
  constructor
  · intro h u
    exact (Fintype.existsUnique_iff_card_one _).mp (h u)
  · intro h u
    exact (Fintype.existsUnique_iff_card_one _).mpr (h u)

theorem children_nonempty (r : ℕ) (u : Node G leader r) :
    (Finset.univ.filter (fun i => parent G leader r i = u)).Nonempty := by
  obtain ⟨i, hi⟩ := forgetMultigraphHistoryClass_surjective G leader r u
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

theorem card_level_le_population (r : ℕ) :
    Fintype.card (Node G leader r) ≤ Fintype.card V := by
  apply Fintype.card_le_of_surjective (classOf G leader r)
  intro c
  exact ⟨c.out, classOf_out G leader r c⟩

theorem card_strict_of_nonflat (r : ℕ) (nonflat : ¬ FlatHistory.Flat G leader r) :
    Fintype.card (Node G leader r) < Fintype.card (Node G leader (r + 1)) := by
  have h := CoreCertificate.card_lt_of_nonflat (parent G leader r) Finset.univ Finset.univ
    (fun i _ => Finset.mem_univ _) (fun u _ => children_nonempty G leader r u) ?_
  · simpa using h
  · intro hflat
    exact nonflat ((flat_iff_child_card_one G leader r).mpr (fun u => hflat u (Finset.mem_univ u)))

/-- There cannot be `n` consecutive strictly refining transitions among
partitions of `n` agents, starting with a nonempty level. -/
theorem exists_flat_step [Nonempty V] :
    ∃ r, r < Fintype.card V ∧ FlatHistory.Flat G leader r := by
  classical
  by_contra h
  push Not at h
  have hzero : 0 < Fintype.card (Node G leader 0) := by
    exact Fintype.card_pos_iff.mpr ⟨classOf G leader 0 (Classical.choice inferInstance)⟩
  have growth : ∀ r, r ≤ Fintype.card V →
      Fintype.card (Node G leader 0) + r ≤ Fintype.card (Node G leader r) := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hs := card_strict_of_nonflat G leader r (h r (by omega))
      omega
  have lower := growth (Fintype.card V) le_rfl
  have upper := card_level_le_population G leader (Fintype.card V)
  omega

/-- The anchor is one plus the largest flat-transition index. -/
theorem exists_last_flat_anchor [Nonempty V] :
    ∃ h, 1 ≤ h ∧ h ≤ Fintype.card V ∧ FlatHistory.Flat G leader (h - 1) ∧
      ∀ r, h ≤ r → r < Fintype.card V → ¬ FlatHistory.Flat G leader r := by
  classical
  let steps := (Finset.range (Fintype.card V)).filter (FlatHistory.Flat G leader)
  have hsteps : steps.Nonempty := by
    obtain ⟨r, hr, hf⟩ := exists_flat_step G leader
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hf⟩⟩
  let k := steps.max' hsteps
  have hk : k ∈ steps := Finset.max'_mem _ _
  obtain ⟨hkrange, hkflat⟩ := Finset.mem_filter.mp hk
  have hklt := Finset.mem_range.mp hkrange
  refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using hkflat
  · intro r hr hrlt hrflat
    have hrsteps : r ∈ steps := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hrflat⟩
    have hrle : r ≤ k := Finset.le_max' steps r hrsteps
    omega

/-- Positive disjoint descendant fibers pass Step 5 for actual anonymities. -/
theorem descendant_count_le_anonymity (h m : ℕ) (hle : h ≤ m)
    (last : Finset (Node G leader m)) (u : Node G leader h) :
    (last.filter (fun i => CoreHistory.ancestor G leader h m i = u)).card ≤ anonymity G leader h u := by
  calc
    (last.filter (fun i => CoreHistory.ancestor G leader h m i = u)).card =
        ∑ _ ∈ last.filter (fun i => CoreHistory.ancestor G leader h m i = u), 1 := by simp
    _ ≤ ∑ i ∈ last.filter (fun i => CoreHistory.ancestor G leader h m i = u),
        anonymity G leader m i := Finset.sum_le_sum fun i _ => anonymity_pos G leader m i
    _ ≤ anonymity G leader h u := CoreHistory.descendants_mass_le G leader h m hle last u

/-- Actual anonymities pass all soundness-relevant Steps 1--5 on an
exhaustive prefix through level `n`; the chosen anchor is the last flat one. -/
theorem exists_true_candidate_checks
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (visible : ∀ r, Finset (Node G leader r))
    (exhaustive : ∀ r, r ≤ Fintype.card V → visible r = Finset.univ) :
    ∃ h, FlatHistory.Flat G leader (h - 1) ∧
      Nonempty (CoreHistory.Checks G leader (Fintype.card V) h visible (anonymity G leader)) := by
  classical
  have hvpos : 0 < Fintype.card V := lt_of_lt_of_le positiveLeaders (Finset.card_le_univ _)
  letI : Nonempty V := Fintype.card_pos_iff.mp hvpos
  obtain ⟨h, hhpos, hhle, hflat, hlast⟩ := exists_last_flat_anchor G leader
  refine ⟨h, hflat, ⟨?_⟩⟩
  exact {
    anchor_positive := hhpos
    anchor_le_final := hhle
    leaders_positive := positiveLeaders
    candidate_positive := fun r hr i _ => anonymity_pos G leader r i
    leader_candidate := by
      intro r hr
      rw [exhaustive r (by omega), Finset.univ_inter]
      exact label_mass_eq G leader r true
    parent_visible := by
      intro r hr i _
      rw [exhaustive r (by omega)]
      exact Finset.mem_univ _
    children_nonempty := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      exact children_nonempty G leader r u
    backward := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      exact (children_mass_eq_iff G leader r Finset.univ u).mpr (fun i _ => Finset.mem_univ i)
    candidate_flow := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      simpa only [Finset.sum_filter] using (flow_balance G leader r u).symm
    anchor_total := by
      rw [exhaustive h hhle]
      exact total_anonymity G leader h
    suffix_nonflat := by
      intro r hr hrlt hflatcounts
      apply hlast r hr hrlt
      apply (flat_iff_child_card_one G leader r).mpr
      intro u
      have hu : u ∈ visible r := by rw [exhaustive r (by omega)]; exact Finset.mem_univ u
      have hc := hflatcounts u hu
      rwa [exhaustive (r + 1) (by omega)] at hc
    suffix_audit := fun u _ => descendant_count_le_anonymity G leader h (Fintype.card V) hhle _ u
  }

/-- Step 3 also has a unique rational solution at the chosen anchor. The
anchor index is written as `r + 1` to keep both adjacent quotient types
definitionally aligned. -/
theorem exists_true_candidate_with_unique_anchor
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (visible : ∀ r, Finset (Node G leader r))
    (exhaustive : ∀ r, r ≤ Fintype.card V → visible r = Finset.univ) :
    ∃ r, r < Fintype.card V ∧
      Nonempty (CoreHistory.Checks G leader (Fintype.card V) (r + 1) visible (anonymity G leader)) ∧
      ∃! z : Node G leader (r + 1) → ℚ,
        FlatLevel.Flow (fun i j => (FlatHistory.weight G leader r i j : ℚ))
          (fun i => (outdegreeLabel G leader r i : ℚ)) z ∧
        (∑ i ∈ FlatHistory.leaders G leader r, z i) = (FlatHistory.leaderCount leader : ℚ) := by
  have hvpos : 0 < Fintype.card V := lt_of_lt_of_le positiveLeaders (Finset.card_le_univ _)
  letI : Nonempty V := Fintype.card_pos_iff.mp hvpos
  obtain ⟨h, hflat, ⟨C⟩⟩ := exists_true_candidate_checks G leader positiveLeaders visible exhaustive
  cases h with
  | zero => have := C.anchor_positive; omega
  | succ r =>
    have hr : r < Fintype.card V := by have := C.anchor_le_final; omega
    have hflat' : FlatHistory.Flat G leader r := by simpa only [Nat.add_sub_cancel] using hflat
    exact ⟨r, hr, ⟨C⟩, FlatHistory.flat_level_unique_solution G leader r hflat'
      (connected (r + 1) (by omega)) positiveLeaders⟩

/-- Mathematical exactness of the certificate test on an exhaustive prefix:
a certificate exists exactly for the true population. The executable
correspondence is proved in ExecutableRefinementEquivalence. -/
theorem certificate_exists_iff_population
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (visible : ∀ r, Finset (Node G leader r))
    (exhaustive : ∀ r, r ≤ Fintype.card V → visible r = Finset.univ) (m : ℕ) :
    (∃ (h : ℕ) (candidate : ∀ r, Node G leader r → ℕ),
      Nonempty (CoreHistory.Checks G leader m h visible candidate)) ↔ m = Fintype.card V := by
  constructor
  · rintro ⟨h, candidate, ⟨C⟩⟩
    exact C.accepted_candidate_eq_population connected
  · intro hm
    subst m
    obtain ⟨h, _, hchecks⟩ := exists_true_candidate_checks G leader positiveLeaders visible exhaustive
    exact ⟨h, anonymity G leader, hchecks⟩

end Counting.CoreCompleteness
