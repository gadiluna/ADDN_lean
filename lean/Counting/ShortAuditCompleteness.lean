import Counting.ShortAuditFlow

namespace Counting.ShortAudit
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- With both input values present, the initial full level has at least
two nodes. This is the one-level improvement over the core audit. -/
theorem initial_card_at_least_two
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V) :
    2 ≤ Fintype.card (Node G leader 0) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp positiveLeaders
  have haleader : leader a = true := (Finset.mem_filter.mp ha).2
  have missing : ∃ b, leader b = false := by
    by_contra hn
    push Not at hn
    have hall : Finset.univ.filter (fun v => leader v = true) = (Finset.univ : Finset V) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Bool.eq_true_of_not_eq_false (hn v)
    have heq := congrArg Finset.card hall
    change FlatHistory.leaderCount leader = Fintype.card V at heq
    omega
  obtain ⟨b, hbleader⟩ := missing
  have hne : classOf G leader 0 a ≠ classOf G leader 0 b := by
    intro heq
    have labels := congrArg (label G leader 0) heq
    simp only [label_classOf, haleader, hbleader, Bool.true_eq_false] at labels
  exact Fintype.one_lt_card_iff.mpr ⟨_, _, hne⟩

theorem exists_short_flat_step
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V) :
    ∃ r, r < Fintype.card V - 1 ∧ FlatHistory.Flat G leader r := by
  classical
  by_contra hn
  push Not at hn
  have initial := initial_card_at_least_two G leader positiveLeaders nonleaders
  have growth : ∀ r, r ≤ Fintype.card V - 1 →
      Fintype.card (Node G leader 0) + r ≤ Fintype.card (Node G leader r) := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hs := CoreCompleteness.card_strict_of_nonflat G leader r (hn r (by omega))
      omega
  have lower := growth (Fintype.card V - 1) le_rfl
  have upper := CoreCompleteness.card_level_le_population G leader (Fintype.card V - 1)
  have positive : 0 < Fintype.card V := lt_trans positiveLeaders nonleaders
  omega

theorem exists_last_short_flat_anchor
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V) :
    ∃ h, 1 ≤ h ∧ h ≤ Fintype.card V - 1 ∧ FlatHistory.Flat G leader (h - 1) ∧
      ∀ r, h ≤ r → r < Fintype.card V - 1 → ¬ FlatHistory.Flat G leader r := by
  classical
  let steps := (Finset.range (Fintype.card V - 1)).filter (FlatHistory.Flat G leader)
  have hsteps : steps.Nonempty := by
    obtain ⟨r, hr, hf⟩ := exists_short_flat_step G leader positiveLeaders nonleaders
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

/-- Actual anonymities pass all arithmetic, structural, and descendant
checks of the shorter audit on an exhaustive prefix through n-1. -/
theorem exists_true_short_checks
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V)
    (visible : ∀ r, Finset (Node G leader r))
    (exhaustive : ∀ r, r ≤ Fintype.card V - 1 → visible r = Finset.univ) :
    ∃ h, FlatHistory.Flat G leader (h - 1) ∧
      Nonempty (Checks G leader (Fintype.card V) h visible (anonymity G leader)) := by
  classical
  obtain ⟨h, hhpos, hhle, hflat, hlast⟩ := exists_last_short_flat_anchor G leader positiveLeaders nonleaders
  refine ⟨h, hflat, ⟨?_⟩⟩
  exact {
    leader_positive := positiveLeaders
    anchor_positive := hhpos
    anchor_le_final := hhle
    anchor_candidate_positive := fun i _ => anonymity_pos G leader h i
    anchor_leader_candidate := by
      rw [exhaustive h hhle, Finset.univ_inter]
      exact label_mass_eq G leader h true
    anchor_total := by
      rw [exhaustive h hhle]
      exact total_anonymity G leader h
    parent_visible := by
      intro r hr i _
      rw [exhaustive r (by omega)]
      exact Finset.mem_univ _
    all_parent_visible := by
      intro r hr i _
      rw [exhaustive r (by omega)]
      exact Finset.mem_univ _
    children_nonempty := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      exact CoreCompleteness.children_nonempty G leader r u
    all_children_nonempty := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      exact CoreCompleteness.children_nonempty G leader r u
    backward := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      exact (children_mass_eq_iff G leader r Finset.univ u).mpr (fun i _ => Finset.mem_univ i)
    candidate_flow := by
      intro r hr u _
      rw [exhaustive (r + 1) (by omega)]
      simpa only [Finset.sum_filter] using (flow_balance G leader r u).symm
    suffix_nonflat := by
      intro r hr hrlt hflatcounts
      apply hlast r hr hrlt
      apply (CoreCompleteness.flat_iff_child_card_one G leader r).mpr
      intro u
      have hu : u ∈ visible r := by rw [exhaustive r (by omega)]; exact Finset.mem_univ u
      have hc := hflatcounts u hu
      rwa [exhaustive (r + 1) (by omega)] at hc
    suffix_audit := fun u _ => CoreCompleteness.descendant_count_le_anonymity G leader h
      (Fintype.card V - 1) hhle _ u
  }

theorem short_prefix_exhaustive
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) (r : ℕ) (hr : r ≤ Fintype.card V - 1) :
    CoreTiming.levelsAt G leader (2 * Fintype.card V - 2) observer r = Finset.univ := by
  have positive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨observer⟩
  apply vista_level_exhaustive G leader connected
  omega

/-- At round 2n-2 every observer accepts the true mathematical shorter
certificate; the last flat anchor has exactly one rational solution, and
the per-level node bound also passes. -/
theorem true_candidate_at_short_round
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) :
    (∀ k, k ≤ Fintype.card V - 1 →
      (CoreTiming.levelsAt G leader (2 * Fintype.card V - 2) observer k).card ≤ Fintype.card V) ∧
    ∃ r, r < Fintype.card V - 1 ∧ FlatHistory.Flat G leader r ∧
      Nonempty (Checks G leader (Fintype.card V) (r + 1)
        (CoreTiming.levelsAt G leader (2 * Fintype.card V - 2) observer) (anonymity G leader)) ∧
      ∃! z : Node G leader (r + 1) → ℚ,
        FlatLevel.Flow (fun i j => (FlatHistory.weight G leader r i j : ℚ))
          (fun i => (outdegreeLabel G leader r i : ℚ)) z ∧
        (∑ i ∈ FlatHistory.leaders G leader r, z i) = (FlatHistory.leaderCount leader : ℚ) := by
  letI : Nonempty V := ⟨observer⟩
  constructor
  · intro k hk
    rw [short_prefix_exhaustive G leader connected observer k hk, Finset.card_univ]
    exact CoreCompleteness.card_level_le_population G leader k
  · obtain ⟨h, hflat, ⟨C⟩⟩ := exists_true_short_checks G leader positiveLeaders nonleaders _
      (short_prefix_exhaustive G leader connected observer)
    cases h with
    | zero => have := C.anchor_positive; omega
    | succ r =>
      have hr : r < Fintype.card V - 1 := by have := C.anchor_le_final; omega
      have hflat' : FlatHistory.Flat G leader r := by simpa only [Nat.add_sub_cancel] using hflat
      exact ⟨r, hr, hflat', ⟨C⟩, FlatHistory.flat_level_unique_solution G leader r hflat'
        (connected (r + 1) (by omega)) positiveLeaders⟩

/-- The rejection half of the paper's Short audit lemma. -/
theorem false_candidate_has_no_short_certificate
    (leaders : 2 ≤ FlatHistory.leaderCount leader)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) (m h : ℕ) (small : m < Fintype.card V)
    (candidate : ∀ r, Node G leader r → ℕ) :
    IsEmpty (Checks G leader m h (CoreTiming.levelsAt G leader (2 * m - 2) observer) candidate) :=
  ⟨fun C => C.false_candidate_impossible small leaders connected⟩

/-- The paper's complete Short audit lemma: at every observer, every
candidate strictly between the known leader count and the population is
rejected at its scheduled round, while the population has a passing last
flat certificate at round 2n-2. `true_candidate_at_short_round` additionally
proves uniqueness of the rational solution and the per-level size checks. -/
theorem short_audit
    (leaders : 2 ≤ FlatHistory.leaderCount leader)
    (nonleaders : FlatHistory.leaderCount leader < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) :
    (∀ m, FlatHistory.leaderCount leader < m → m < Fintype.card V →
      ∀ h candidate,
        IsEmpty (Checks G leader m h (CoreTiming.levelsAt G leader (2 * m - 2) observer) candidate)) ∧
    ∃ r, r < Fintype.card V - 1 ∧ FlatHistory.Flat G leader r ∧
      Nonempty (Checks G leader (Fintype.card V) (r + 1)
        (CoreTiming.levelsAt G leader (2 * Fintype.card V - 2) observer) (anonymity G leader)) := by
  constructor
  · intro m _ small h candidate
    exact false_candidate_has_no_short_certificate G leader leaders connected observer m h small candidate
  · obtain ⟨_, r, hr, flat, checks, _⟩ := true_candidate_at_short_round G leader (by omega)
      nonleaders connected observer
    exact ⟨r, hr, flat, checks⟩

end Counting.ShortAudit
