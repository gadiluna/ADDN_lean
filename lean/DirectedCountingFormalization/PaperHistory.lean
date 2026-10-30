import DirectedCountingFormalization.MultigraphPairedHistory
import DirectedCountingFormalization.WeightedEdgeCounting

/-!
# Concrete history-tree accounting for the STOC manuscript

All nodes below are actual quotient classes of the multiplicity-preserving,
late-outdegree history relation. No symmetry or unique-leader assumption is
used. The selected finite sets can be any visible sublevel; consequently the
accounting statements apply to vistas once their visibility is instantiated.
The root at level -1 is handled separately as the whole carrier.
-/

namespace DirectedCounting.PaperHistory

open scoped BigOperators

variable {V Input : Type*} [Fintype V]
variable (G : Nat → V → V → Nat) (input : V → Input)

abbrev Node (t : Nat) := MultigraphHistoryClass G input t

noncomputable instance nodeFintype (t : Nat) : Fintype (Node G input t) :=
  Fintype.ofFinite _

noncomputable instance nodeDecidableEq (t : Nat) : DecidableEq (Node G input t) :=
  Classical.decEq _

noncomputable def classOf (t : Nat) (v : V) : Node G input t := Quotient.mk'' v

noncomputable def fiber (t : Nat) (c : Node G input t) : Finset V := by
  classical
  exact Finset.univ.filter (fun v ↦ classOf G input t v = c)

noncomputable def anonymity (t : Nat) (c : Node G input t) : Nat :=
  (fiber G input t c).card

@[simp] theorem mem_fiber (t : Nat) (c : Node G input t) (v : V) :
    v ∈ fiber G input t c ↔ classOf G input t v = c := by
  classical
  simp [fiber]

@[simp] theorem classOf_out (t : Nat) (c : Node G input t) :
    classOf G input t c.out = c := Quotient.out_eq' c

theorem anonymity_pos (t : Nat) (c : Node G input t) :
    0 < anonymity G input t c := by
  apply Finset.card_pos.mpr
  exact ⟨c.out, (mem_fiber G input t c c.out).mpr (classOf_out G input t c)⟩

theorem classOf_eq_iff (t : Nat) (u v : V) :
    classOf G input t u = classOf G input t v ↔
      sameMultigraphHistory G input t u v := Quotient.eq

theorem sameHistory_of_mem_fiber (t : Nat) (c : Node G input t)
    {u v : V} (hu : u ∈ fiber G input t c) (hv : v ∈ fiber G input t c) :
    sameMultigraphHistory G input t u v := by
  apply (classOf_eq_iff G input t u v).mp
  exact (mem_fiber G input t c u).mp hu |>.trans
    ((mem_fiber G input t c v).mp hv).symm

/-- Disjointness in H1 is derived from quotient classes, not assumed. -/
theorem fibers_pairwiseDisjoint (t : Nat) (visible : Finset (Node G input t)) :
    (visible : Set (Node G input t)).PairwiseDisjoint (fiber G input t) := by
  intro a _ b _ hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  exact hab (((mem_fiber G input t a v).mp hva).symm.trans
    ((mem_fiber G input t b v).mp hvb))

/-- Visible mass counts exactly the agents in the selected history classes. -/
theorem sum_anonymity_eq_card_filter (t : Nat)
    (visible : Finset (Node G input t)) :
    (∑ c ∈ visible, anonymity G input t c) =
      (Finset.univ.filter (fun v ↦ classOf G input t v ∈ visible)).card := by
  classical
  exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ visible
    (classOf G input t)

/-- H1: a selected level represents at most the total population. -/
theorem visible_mass_le (t : Nat) (visible : Finset (Node G input t)) :
    (∑ c ∈ visible, anonymity G input t c) ≤ Fintype.card V := by
  classical
  rw [sum_anonymity_eq_card_filter]
  exact Finset.card_le_univ _

/-- H1: equality holds precisely for an exhaustive level. -/
theorem visible_mass_eq_iff_exhaustive (t : Nat)
    (visible : Finset (Node G input t)) :
    (∑ c ∈ visible, anonymity G input t c) = Fintype.card V ↔
      visible = Finset.univ := by
  classical
  rw [sum_anonymity_eq_card_filter]
  constructor
  · intro hmass
    have hall := Finset.eq_univ_of_card _ hmass
    apply Finset.eq_univ_of_forall
    intro c
    have hmem : c.out ∈ Finset.univ.filter
        (fun v ↦ classOf G input t v ∈ visible) := by rw [hall]; simp
    simpa using hmem
  · intro h
    simp [h]

@[simp] theorem total_anonymity (t : Nat) :
    (∑ c : Node G input t, anonymity G input t c) = Fintype.card V :=
  (visible_mass_eq_iff_exhaustive G input t Finset.univ).mpr rfl

noncomputable def parent (t : Nat) : Node G input (t + 1) → Node G input t :=
  forgetMultigraphHistoryClass G input t

@[simp] theorem parent_classOf (t : Nat) (v : V) :
    parent G input t (classOf G input (t + 1) v) = classOf G input t v := rfl

/-- Every concrete child fiber is contained in its parent's fiber. -/
theorem fiber_subset_parent (t : Nat) (c : Node G input (t + 1)) :
    fiber G input (t + 1) c ⊆ fiber G input t (parent G input t c) := by
  intro v hv
  apply (mem_fiber G input t _ v).mpr
  have h := congrArg (parent G input t) ((mem_fiber G input (t + 1) c v).mp hv)
  exact h

/-- H1: selected children represent exactly their selected agents. -/
theorem children_mass_eq_card_filter (t : Nat)
    (visible : Finset (Node G input (t + 1))) (p : Node G input t) :
    (∑ c ∈ visible.filter (fun c ↦ parent G input t c = p),
      anonymity G input (t + 1) c) =
    ((fiber G input t p).filter
      (fun v ↦ classOf G input (t + 1) v ∈ visible)).card := by
  classical
  rw [sum_anonymity_eq_card_filter]
  congr 1
  ext v
  simp [fiber, and_comm]

/-- H1: hidden children can only decrease the represented parent mass. -/
theorem children_mass_le (t : Nat)
    (visible : Finset (Node G input (t + 1))) (p : Node G input t) :
    (∑ c ∈ visible.filter (fun c ↦ parent G input t c = p),
      anonymity G input (t + 1) c) ≤ anonymity G input t p := by
  classical
  rw [children_mass_eq_card_filter]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- H1: selected children account for the whole parent exactly when none is hidden. -/
theorem children_mass_eq_iff (t : Nat)
    (visible : Finset (Node G input (t + 1))) (p : Node G input t) :
    (∑ c ∈ visible.filter (fun c ↦ parent G input t c = p),
      anonymity G input (t + 1) c) = anonymity G input t p ↔
    ∀ c, parent G input t c = p → c ∈ visible := by
  classical
  rw [children_mass_eq_card_filter]
  change _ = (fiber G input t p).card ↔ _
  constructor
  · intro heq c hc
    have hsets := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset (fun v ↦ classOf G input (t + 1) v ∈ visible)
        (fiber G input t p)) (Nat.le_of_eq heq.symm)
    have hparent : c.out ∈ fiber G input t p := by
      apply (mem_fiber G input t p c.out).mpr
      rw [← parent_classOf G input t c.out, classOf_out, hc]
    have hselected : c.out ∈ (fiber G input t p).filter
        (fun v ↦ classOf G input (t + 1) v ∈ visible) := by
      rw [hsets]; exact hparent
    simpa using (Finset.mem_filter.mp hselected).2
  · intro hall
    congr 1
    apply Finset.filter_eq_self.mpr
    intro v hv
    apply hall
    simpa using (mem_fiber G input t p v).mp hv

/-- Input labels are constant on each concrete history fiber. -/
theorem input_eq_of_mem_fiber (t : Nat) (c : Node G input t)
    {u v : V} (hu : u ∈ fiber G input t c) (hv : v ∈ fiber G input t c) :
    input u = input v := by
  exact sameMultigraphHistory_of_le (Nat.zero_le t)
    (sameHistory_of_mem_fiber G input t c hu hv)

noncomputable def label (t : Nat) (c : Node G input t) : Input := input c.out

@[simp] theorem label_classOf (t : Nat) (v : V) :
    label G input t (classOf G input t v) = input v := by
  apply input_eq_of_mem_fiber G input t (classOf G input t v)
  · exact (mem_fiber G input t _ _).mpr (classOf_out G input t _)
  · simp

theorem label_parent (t : Nat) (c : Node G input (t + 1)) :
    label G input t (parent G input t c) = label G input (t + 1) c := by
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective c
  exact (label_classOf G input t v).trans (label_classOf G input (t + 1) v).symm

/-- H2: all visible nodes of any one input label account for at most its agents.
For Boolean inputs and `value = true`, this is leader accounting. -/
theorem label_mass_le [DecidableEq Input] (t : Nat)
    (visible : Finset (Node G input t)) (value : Input) :
    (∑ c ∈ visible.filter (fun c ↦ label G input t c = value),
      anonymity G input t c) ≤
    (Finset.univ.filter (fun v ↦ input v = value)).card := by
  classical
  rw [sum_anonymity_eq_card_filter]
  apply Finset.card_le_card
  intro v hv
  simpa using (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2

/-- H2: exhaustive levels preserve exactly the number of leaders. -/
theorem label_mass_eq [DecidableEq Input] (t : Nat) (value : Input) :
    (∑ c ∈ Finset.univ.filter (fun c : Node G input t ↦ label G input t c = value),
      anonymity G input t c) =
    (Finset.univ.filter (fun v ↦ input v = value)).card := by
  classical
  rw [sum_anonymity_eq_card_filter]
  simp

/-- The label of a black edge is the outdegree of any agent in its child fiber. -/
noncomputable def outdegreeLabel (t : Nat) (c : Node G input (t + 1)) : Nat :=
  multigraphOutdegree G (t + 1) c.out

/-- The label of a red edge is the incoming multiplicity from its source fiber. -/
noncomputable def redMultiplicity (t : Nat)
    (p : Node G input t) (c : Node G input (t + 1)) : Nat :=
  weightedIncomingCount (G (t + 1)) (fiber G input t p) c.out

theorem outdegree_eq_label (t : Nat) (c : Node G input (t + 1))
    {v : V} (hv : v ∈ fiber G input (t + 1) c) :
    multigraphOutdegree G (t + 1) v = outdegreeLabel G input t c := by
  exact (sameHistory_of_mem_fiber G input (t + 1) c hv
    ((mem_fiber G input (t + 1) c c.out).mpr (classOf_out G input _ c))).2.1

theorem incoming_fiber_eq_history (t : Nat) (p : Node G input t) (v : V) :
    weightedIncomingCount (G (t + 1)) (fiber G input t p) v =
      weightedIncomingFromClass (G (t + 1)) (sameMultigraphHistory G input t) v p.out := by
  classical
  unfold weightedIncomingCount weightedIncomingFromClass fiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  have hequiv : classOf G input t u = p ↔ sameMultigraphHistory G input t u p.out := by
    constructor
    · intro h
      exact (classOf_eq_iff G input t u p.out).mp
        (h.trans (classOf_out G input t p).symm)
    · intro h
      exact ((classOf_eq_iff G input t u p.out).mpr h).trans
        (classOf_out G input t p)
  simp only [hequiv]

theorem incoming_eq_redMultiplicity (t : Nat)
    (p : Node G input t) (c : Node G input (t + 1))
    {v : V} (hv : v ∈ fiber G input (t + 1) c) :
    weightedIncomingCount (G (t + 1)) (fiber G input t p) v =
      redMultiplicity G input t p c := by
  unfold redMultiplicity
  rw [incoming_fiber_eq_history, incoming_fiber_eq_history]
  exact (sameHistory_of_mem_fiber G input (t + 1) c hv
    ((mem_fiber G input (t + 1) c c.out).mpr (classOf_out G input _ c))).2.2 p.out

/-- H3, incoming identity, including arbitrary parallel arcs and loops. -/
theorem flow_incoming (t : Nat)
    (p : Node G input t) (c : Node G input (t + 1)) :
    weightedEdgeCount (G (t + 1)) (fiber G input t p) (fiber G input (t + 1) c) =
      redMultiplicity G input t p c * anonymity G input (t + 1) c := by
  exact weightedEdgeCount_eq_mul_card_of_constant_incoming _ _ _ _
    (fun _ hv ↦ incoming_eq_redMultiplicity G input t p c hv)

/-- H3, outgoing identity, including arbitrary parallel arcs and loops. -/
theorem flow_outgoing (t : Nat) (c : Node G input (t + 1)) :
    weightedEdgeCount (G (t + 1)) (fiber G input (t + 1) c) Finset.univ =
      outdegreeLabel G input t c * anonymity G input (t + 1) c := by
  rw [weightedEdgeCount_transpose]
  apply weightedEdgeCount_eq_mul_card_of_constant_incoming
  intro v hv
  exact outdegree_eq_label G input t c hv

/-- The full level partitions the population. -/
theorem all_fibers_union [DecidableEq V] (t : Nat) :
    Finset.univ.biUnion (fiber G input t) = (Finset.univ : Finset V) := by
  classical
  apply Finset.eq_univ_of_forall
  intro v
  apply Finset.mem_biUnion.mpr
  exact ⟨classOf G input t v, Finset.mem_univ _, by simp⟩

/-- The full set of children partitions its parent fiber. -/
theorem children_fibers_union [DecidableEq V] (t : Nat) (p : Node G input t) :
    (Finset.univ.filter (fun c : Node G input (t + 1) ↦ parent G input t c = p)).biUnion
      (fiber G input (t + 1)) = fiber G input t p := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_fiber]
  constructor
  · rintro ⟨c, hc, hvc⟩
    rw [← hvc, parent_classOf] at hc
    exact hc
  · intro hv
    exact ⟨classOf G input (t + 1) v, by simpa using hv, rfl⟩

/-- H3: counting all arcs from an old fiber by heads or tails gives Flow. -/
theorem flow_balance (t : Nat) (p : Node G input t) :
    (∑ c : Node G input (t + 1),
      redMultiplicity G input t p c * anonymity G input (t + 1) c) =
    ∑ c ∈ Finset.univ.filter (fun c : Node G input (t + 1) ↦ parent G input t c = p),
      outdegreeLabel G input t c * anonymity G input (t + 1) c := by
  classical
  calc
    _ = ∑ c : Node G input (t + 1),
        weightedEdgeCount (G (t + 1)) (fiber G input t p)
          (fiber G input (t + 1) c) := by
      apply Finset.sum_congr rfl
      intro c _
      exact (flow_incoming G input t p c).symm
    _ = weightedEdgeCount (G (t + 1)) (fiber G input t p) Finset.univ := by
      rw [← weightedEdgeCount_biUnion _ _ _ _ (fibers_pairwiseDisjoint G input _ _),
        all_fibers_union]
    _ = weightedEdgeCount (fun v u ↦ G (t + 1) u v) Finset.univ
        (fiber G input t p) := weightedEdgeCount_transpose _ _ _
    _ = ∑ c ∈ Finset.univ.filter
        (fun c : Node G input (t + 1) ↦ parent G input t c = p),
        weightedEdgeCount (fun v u ↦ G (t + 1) u v) Finset.univ
          (fiber G input (t + 1) c) := by
      rw [← children_fibers_union G input t p]
      exact weightedEdgeCount_biUnion _ _ _ _ (fibers_pairwiseDisjoint G input _ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← weightedEdgeCount_transpose (G (t + 1))]
      exact flow_outgoing G input t c

end DirectedCounting.PaperHistory
