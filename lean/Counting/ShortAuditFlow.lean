import Counting.ShortAuditView

namespace Counting.ShortAudit
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- The number of agents of S in one full history fiber. -/
noncomputable def restrictedMass (S : Finset V) (r : ℕ) (c : Node G leader r) : ℕ :=
  (S.filter (fun v => classOf G leader r v = c)).card

theorem restrictedMass_eq_anonymity (S : Finset V) (r : ℕ) (c : Node G leader r)
    (inside : fiber G leader r c ⊆ S) :
    restrictedMass G leader S r c = anonymity G leader r c := by
  unfold restrictedMass anonymity
  congr 1
  ext v
  simp only [Finset.mem_filter, mem_fiber]
  exact ⟨fun hv => hv.2, fun hv => ⟨inside ((mem_fiber G leader r c v).mpr hv), hv⟩⟩

theorem restrictedMass_partition (S : Finset V) (r : ℕ)
    (nodes : Finset (Node G leader (r + 1)))
    (represented : ∀ v ∈ S, classOf G leader (r + 1) v ∈ nodes) (u : Node G leader r) :
    (∑ c ∈ nodes.filter (fun c => parent G leader r c = u), restrictedMass G leader S (r + 1) c) =
      restrictedMass G leader S r u := by
  classical
  rw [show (∑ c ∈ nodes.filter (fun c => parent G leader r c = u), restrictedMass G leader S (r + 1) c) =
      (S.filter (fun v => classOf G leader (r + 1) v ∈ nodes.filter (fun c => parent G leader r c = u))).card from
    Finset.sum_card_fiberwise_eq_card_filter S _ (classOf G leader (r + 1))]
  congr 1
  ext v
  simp only [Finset.mem_filter, parent_classOf]
  exact ⟨fun hv => ⟨hv.1, hv.2.2⟩, fun hv => ⟨hv.1, represented v hv.1, hv.2⟩⟩

theorem restricted_incoming_sum (S : Finset V) (r : ℕ)
    (nodes : Finset (Node G leader (r + 1)))
    (represented : ∀ v ∈ S, classOf G leader (r + 1) v ∈ nodes) (u : Node G leader r) :
    (∑ c ∈ nodes, redMultiplicity G leader r u c * restrictedMass G leader S (r + 1) c) =
      weightedEdgeCount (G (r + 1)) (fiber G leader r u) S := by
  calc
    _ = ∑ c ∈ nodes, ∑ v ∈ S.filter (fun v => classOf G leader (r + 1) v = c),
        weightedIncomingCount (G (r + 1)) (fiber G leader r u) v := by
      apply Finset.sum_congr rfl
      intro c _
      symm
      calc
        _ = ∑ _v ∈ S.filter (fun v => classOf G leader (r + 1) v = c), redMultiplicity G leader r u c := by
          apply Finset.sum_congr rfl
          intro v hv
          exact incoming_eq_redMultiplicity G leader r u c ((mem_fiber G leader (r + 1) c v).mpr (Finset.mem_filter.mp hv).2)
        _ = _ := by simp [restrictedMass, Nat.mul_comm]
    _ = _ := Finset.sum_fiberwise_of_maps_to represented _

/-- Equality of all outgoing multiplicity with the part landing in S
rules out every individual arc to its complement. -/
theorem no_arc_of_edge_count_eq (edge : V → V → ℕ) (A S : Finset V)
    (equal : weightedEdgeCount edge A Finset.univ = weightedEdgeCount edge A S) :
    ∀ a ∈ A, ∀ b, b ∉ S → edge a b = 0 := by
  classical
  have sums : (∑ b : V, if b ∈ S then weightedIncomingCount edge A b else 0) =
      ∑ b : V, weightedIncomingCount edge A b := by
    rw [← Finset.sum_filter]
    simpa only [weightedEdgeCount, Finset.filter_mem_eq_inter, Finset.univ_inter] using equal.symm
  have each := total_credit_eq_forces_local_eq Finset.univ (weightedIncomingCount edge A)
    (fun b => if b ∈ S then weightedIncomingCount edge A b else 0)
    (fun b _ => by split <;> omega) sums
  intro a ha b hb
  have hzero := each b (Finset.mem_univ b)
  simp only [if_neg hb] at hzero
  have hle := Finset.single_le_sum (f := fun a => edge a b) (fun _ _ => Nat.zero_le _) ha
  change edge a b ≤ weightedIncomingCount edge A b at hle
  omega

/-- The checked flow equation with intersection counts has exactly the
paper's no-escape consequence for every full old fiber contained in S. -/
theorem noEscape_of_restricted_flow (S : Finset V) (r : ℕ)
    (old : Finset (Node G leader r)) (next : Finset (Node G leader (r + 1)))
    (candidate : Node G leader (r + 1) → ℕ)
    (oldRepresented : ∀ v ∈ S, classOf G leader r v ∈ old)
    (newRepresented : ∀ v ∈ S, classOf G leader (r + 1) v ∈ next)
    (values : ∀ c ∈ next, candidate c = restrictedMass G leader S (r + 1) c)
    (flow : ∀ u ∈ old,
      (∑ c ∈ next, if parent G leader r c = u then outdegreeLabel G leader r c * candidate c else 0) =
      ∑ c ∈ next, redMultiplicity G leader r u c * candidate c) :
    ForwardFibers.NoEscape G leader S r := by
  classical
  intro u hu
  have huvis : u ∈ old := by
    have := oldRepresented u.out (hu (by simp))
    simpa using this
  have allChildren : ∀ c, parent G leader r c = u → c ∈ next := by
    intro c hc
    have hsubset : fiber G leader (r + 1) c ⊆ S := by
      have hp := fiber_subset_parent G leader r c
      rw [hc] at hp
      exact hp.trans hu
    simpa using newRepresented c.out (hsubset (by simp))
  have childset : next.filter (fun c => parent G leader r c = u) =
      Finset.univ.filter (fun c => parent G leader r c = u) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hc => hc.2, fun hc => ⟨allChildren c hc, hc⟩⟩
  have outgoing : (∑ c ∈ next, if parent G leader r c = u then outdegreeLabel G leader r c * candidate c else 0) =
      weightedEdgeCount (G (r + 1)) (fiber G leader r u) Finset.univ := by
    rw [← Finset.sum_filter]
    calc
      _ = ∑ c ∈ next.filter (fun c => parent G leader r c = u),
          outdegreeLabel G leader r c * anonymity G leader (r + 1) c := by
        apply Finset.sum_congr rfl
        intro c hc
        obtain ⟨hcn, hcp⟩ := Finset.mem_filter.mp hc
        rw [values c hcn, restrictedMass_eq_anonymity G leader S (r + 1) c]
        have hp := fiber_subset_parent G leader r c
        rw [hcp] at hp
        exact hp.trans hu
      _ = ∑ c : Node G leader (r + 1), redMultiplicity G leader r u c * anonymity G leader (r + 1) c := by
        rw [childset]
        exact (flow_balance G leader r u).symm
      _ = _ := by
        calc
          _ = ∑ c : Node G leader (r + 1),
              weightedEdgeCount (G (r + 1)) (fiber G leader r u) (fiber G leader (r + 1) c) :=
            Finset.sum_congr rfl (fun c _ => (flow_incoming G leader r u c).symm)
          _ = _ := by
            rw [← weightedEdgeCount_biUnion _ _ _ _ (fibers_pairwiseDisjoint G leader (r + 1) _), all_fibers_union]
  have incoming : (∑ c ∈ next, redMultiplicity G leader r u c * candidate c) =
      weightedEdgeCount (G (r + 1)) (fiber G leader r u) S := by
    calc
      _ = ∑ c ∈ next, redMultiplicity G leader r u c * restrictedMass G leader S (r + 1) c :=
        Finset.sum_congr rfl (fun c hc => congrArg (fun n => redMultiplicity G leader r u c * n) (values c hc))
      _ = _ := restricted_incoming_sum G leader S r next newRepresented u
  exact no_arc_of_edge_count_eq (G (r + 1)) (fiber G leader r u) S
    (outgoing.symm.trans ((flow u huvis).trans incoming))

namespace Checks
variable {G leader} {m h : ℕ} {candidate : ∀ r, Node G leader r → ℕ} {observer : V}
  (C : Checks G leader m h (CoreTiming.levelsAt G leader (2 * m - 2) observer) candidate)

include C

/-- After anchor rigidity, backward propagation counts precisely each
earlier fiber's intersection with the represented m-agent set. -/
theorem false_candidate_intersections (small : m < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    ∀ r, r ≤ h → ∀ c ∈ CoreTiming.levelsAt G leader (2 * m - 2) observer r,
      candidate r c = restrictedMass G leader
        (agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h)) r c := by
  classical
  let visible := CoreTiming.levelsAt G leader (2 * m - 2) observer
  let S := agents G leader h (visible h)
  have anchor := (C.false_anchor_rigidity small connected).1
  have represented : ∀ r, r ≤ h → ∀ v ∈ S, classOf G leader r v ∈ visible r := by
    intro r hr v hv
    have hsub := agents_refine G leader r h hr visible C.parent_visible
    exact (mem_agents G leader r _ v).mp (hsub hv)
  have base : ∀ c ∈ visible h, candidate h c = restrictedMass G leader S h c := by
    intro c hc
    rw [← anchor c hc]
    symm
    apply restrictedMass_eq_anonymity
    intro v hv
    apply (mem_agents G leader h _ v).mpr
    simpa only [(mem_fiber G leader h c v).mp hv] using hc
  intro r hr
  apply Nat.decreasingInduction (motive := fun r _ => ∀ c ∈ visible r,
    candidate r c = restrictedMass G leader S r c) ?_ base hr
  intro k hk ih c hc
  rw [← C.backward k hk c hc]
  calc
    _ = ∑ d ∈ (visible (k + 1)).filter (fun d => parent G leader k d = c),
        restrictedMass G leader S (k + 1) d :=
      Finset.sum_congr rfl (fun d hd => ih d (Finset.mem_filter.mp hd).1)
    _ = _ := restrictedMass_partition G leader S k (visible (k + 1)) (represented (k + 1) (by omega)) c

theorem false_represented_contains_leaders (small : m < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    ∀ v, leader v = true → v ∈ agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h) := by
  classical
  let visible := CoreTiming.levelsAt G leader (2 * m - 2) observer
  let S := agents G leader h (visible h)
  have vals := (C.false_anchor_rigidity small connected).1
  have leaderMass : (∑ c ∈ visible h ∩ Finset.univ.filter (fun c => label G leader h c = true),
      anonymity G leader h c) = FlatHistory.leaderCount leader := by
    rw [← C.anchor_leader_candidate]
    exact Finset.sum_congr rfl (fun c hc => vals c (Finset.mem_inter.mp hc).1)
  rw [sum_anonymity_eq_card_filter] at leaderMass
  have leaderSet : Finset.univ.filter (fun v => classOf G leader h v ∈
      visible h ∩ Finset.univ.filter (fun c => label G leader h c = true)) = S.filter (fun v => leader v = true) := by
    ext v
    simp [S, agents, label_classOf]
  rw [leaderSet] at leaderMass
  have equality : S.filter (fun v => leader v = true) = Finset.univ.filter (fun v => leader v = true) := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
    · exact leaderMass.ge
  intro v hv
  have hm : v ∈ S.filter (fun v => leader v = true) := by rw [equality]; simp [hv]
  exact (Finset.mem_filter.mp hm).1

/-- A hypothetical false certificate satisfies the no-escape premise of
the forward-fibers lemma throughout its first m-1 rounds. -/
theorem false_noEscape (small : m < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    ∀ r, r < m - 1 → ForwardFibers.NoEscape G leader
      (agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h)) r := by
  classical
  let visible := CoreTiming.levelsAt G leader (2 * m - 2) observer
  have final := C.false_anchor_is_final small connected
  have represented : ∀ r, r ≤ h → ∀ v ∈ agents G leader h (visible h), classOf G leader r v ∈ visible r := by
    intro r hr v hv
    exact (mem_agents G leader r _ v).mp ((agents_refine G leader r h hr visible C.parent_visible) hv)
  intro r hr
  exact noEscape_of_restricted_flow G leader _ r (visible r) (visible (r + 1)) (candidate (r + 1))
    (represented r (by omega)) (represented (r + 1) (by omega))
    (C.false_candidate_intersections small connected (r + 1) (by omega)) (C.candidate_flow r (by omega))

/-- Complete mathematical rejection of every smaller candidate in the
multiple-leader short audit, on an actual observer vista at round 2m-2. -/
theorem false_candidate_impossible (small : m < Fintype.card V)
    (leaders : 2 ≤ FlatHistory.leaderCount leader)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) : False := by
  classical
  let S := agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h)
  have card := (C.false_anchor_rigidity small connected).2.1
  have proper : S ≠ Finset.univ := by
    intro eq
    have := congrArg Finset.card eq
    rw [Finset.card_univ] at this
    change S.card = m at card
    omega
  have bound := ForwardFibers.fibers_inside_proper_subset G leader S (m - 1) (FlatHistory.leaderCount leader)
    proper (C.false_represented_contains_leaders small connected) rfl (by omega) connected
    (C.false_noEscape small connected)
  change S.card = m at card
  have hpos := C.anchor_positive
  have hle := C.anchor_le_final
  omega

end Checks
end Counting.ShortAudit
