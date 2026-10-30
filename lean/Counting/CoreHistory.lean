import Counting.CoreCertificate
import Counting.FlatHistory

/-!
# Core-certificate soundness on concrete multigraph history trees

Actual fibers, their masses, parent refinement, outgoing labels, incoming
multiplicities and connected support are derived from the execution. The
only certificate premises below concern selected visible nodes, candidate
anonymities, and the explicit structural/flow/suffix audits.
-/

namespace Counting.CoreHistory

open DirectedCounting DirectedCounting.PaperHistory

variable {V : Type*} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- Ancestor in an earlier quotient level. -/
noncomputable def ancestor (h m : ℕ) (c : Node G leader m) : Node G leader h :=
  classOf G leader h c.out

theorem ancestor_classOf (h m : ℕ) (hle : h ≤ m) (v : V) :
    ancestor G leader h m (classOf G leader m v) = classOf G leader h v := by
  apply (classOf_eq_iff G leader h _ _).mpr
  apply sameMultigraphHistory_of_le hle
  exact (classOf_eq_iff G leader m _ _).mp (classOf_out G leader m _)

@[simp] theorem ancestor_self (h : ℕ) (c : Node G leader h) :
    ancestor G leader h h c = c := classOf_out G leader h c

theorem ancestor_succ (h r : ℕ) (hle : h ≤ r) (c : Node G leader (r + 1)) :
    ancestor G leader h (r + 1) c = ancestor G leader h r (parent G leader r c) := by
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective c
  change ancestor G leader h (r + 1) (classOf G leader (r + 1) v) =
    ancestor G leader h r (parent G leader r (classOf G leader (r + 1) v))
  rw [parent_classOf, ancestor_classOf G leader h r hle,
    ancestor_classOf G leader h (r + 1) (by omega)]

/-- Visibility of immediate parents propagates to all earlier ancestors. -/
theorem ancestor_visible_of_parent_visible (h m : ℕ) (hle : h ≤ m)
    (visible : ∀ r, Finset (Node G leader r))
    (parents : ∀ r, r < m → ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r) :
    ∀ i ∈ visible m, ancestor G leader h m i ∈ visible h := by
  have descend : ∀ r, h ≤ r → r ≤ m →
      ∀ i ∈ visible r, ancestor G leader h r i ∈ visible h := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      intro _ i hi
      simpa only [ancestor_self] using hi
    | succ r hr ih =>
      intro hrm i hi
      rw [ancestor_succ G leader h r hr]
      exact ih (by omega) _ (parents r (by omega) i hi)
  exact descend m hle le_rfl

/-- The audit requiring a visible child at every step supplies at least one
visible final descendant of every visible anchor node. -/
theorem descendants_nonempty_of_children (h m : ℕ) (hle : h ≤ m)
    (visible : ∀ r, Finset (Node G leader r))
    (children : ∀ r, r < m → ∀ u ∈ visible r,
      ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty) :
    ∀ u ∈ visible h, ((visible m).filter (fun i => ancestor G leader h m i = u)).Nonempty := by
  have extend : ∀ r, h ≤ r → r ≤ m → ∀ u ∈ visible h,
      ∃ i ∈ visible r, ancestor G leader h r i = u := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      intro _ u hu
      exact ⟨u, hu, ancestor_self G leader h u⟩
    | succ r hr ih =>
      intro hrm u hu
      obtain ⟨i, hi, hiancestor⟩ := ih (by omega) u hu
      obtain ⟨j, hj⟩ := children r (by omega) i hi
      obtain ⟨hjvisible, hjparent⟩ := Finset.mem_filter.mp hj
      refine ⟨j, hjvisible, ?_⟩
      rw [ancestor_succ G leader h r hr, hjparent, hiancestor]
  intro u hu
  obtain ⟨i, hi, ha⟩ := extend m hle le_rfl u hu
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩⟩

/-- Disjoint descendant fibers occupy at most the ancestor's actual fiber. -/
theorem descendants_mass_le (h m : ℕ) (hle : h ≤ m)
    (last : Finset (Node G leader m)) (u : Node G leader h) :
    (∑ i ∈ last.filter (fun i => ancestor G leader h m i = u), anonymity G leader m i) ≤
      anonymity G leader h u := by
  classical
  rw [sum_anonymity_eq_card_filter]
  apply Finset.card_le_card
  intro v hv
  have hselected := (Finset.mem_filter.mp hv).2
  have hancestor := (Finset.mem_filter.mp hselected).2
  rw [ancestor_classOf G leader h m hle] at hancestor
  exact (mem_fiber G leader h u v).mpr hancestor

/-- Passed candidate checks on selected levels of the actual history tree.
The visibility and descendant fields are structural obligations supplied
by a vista construction; they do not assert correctness of the candidate. -/
structure Checks (m h : ℕ)
    (visible : ∀ r, Finset (Node G leader r))
    (candidate : ∀ r, Node G leader r → ℕ) where
  anchor_positive : 1 ≤ h
  anchor_le_final : h ≤ m
  leaders_positive : 0 < FlatHistory.leaderCount leader
  candidate_positive : ∀ r, r ≤ h → ∀ i ∈ visible r, 0 < candidate r i
  leader_candidate : ∀ r, r ≤ h →
    (∑ i ∈ visible r ∩ Finset.univ.filter (fun c => label G leader r c = true), candidate r i) =
      FlatHistory.leaderCount leader
  parent_visible : ∀ r, r < m → ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r
  children_nonempty : ∀ r, r < m → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty
  backward : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
      candidate r u
  candidate_flow : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1),
      if parent G leader r i = u then outdegreeLabel G leader r i * candidate (r + 1) i else 0) =
    ∑ i ∈ visible (r + 1), redMultiplicity G leader r u i * candidate (r + 1) i
  anchor_total : (∑ i ∈ visible h, candidate h i) = m
  suffix_nonflat : ∀ r, h ≤ r → r < m →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => parent G leader r i = u)).card = 1
  suffix_audit : ∀ u ∈ visible h,
    ((visible m).filter (fun i => ancestor G leader h m i = u)).card ≤ candidate h u

namespace Checks

variable {G leader} {m h : ℕ}
  {visible : ∀ r, Finset (Node G leader r)} {candidate : ∀ r, Node G leader r → ℕ}
  (C : Checks G leader m h visible candidate)

/-- Constructing the abstract core certificate discharges all actual-flow,
partition, positivity, population and leader-count hypotheses. -/
noncomputable def toAuditedCore
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    CoreCertificate.AuditedCorePrefix (Node G leader) m h (Fintype.card V)
      (FlatHistory.leaderCount leader) where
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  leader_positive := C.leaders_positive
  visible := visible
  leaders := fun r => Finset.univ.filter (fun c => label G leader r c = true)
  parent := parent G leader
  actual := anonymity G leader
  candidate := candidate
  degree := outdegreeLabel G leader
  weight := redMultiplicity G leader
  actual_positive := fun r _ => anonymity_pos G leader r
  candidate_positive := C.candidate_positive
  population := fun r _ => total_anonymity G leader r
  leader_actual := fun r _ => label_mass_eq G leader r true
  leader_candidate := C.leader_candidate
  parent_visible := C.parent_visible
  children_nonempty := C.children_nonempty
  partition := fun r _ u => (children_mass_eq_iff G leader r Finset.univ u).mpr
    (fun c _ => Finset.mem_univ c)
  backward := C.backward
  actual_flow := by
    intro r _ u
    simpa only [Finset.sum_filter] using (flow_balance G leader r u).symm
  candidate_flow := C.candidate_flow
  connected := fun r _ => FlatHistory.weight_stronglyConnected G leader r (connected (r + 1) (by omega))
  anchor_total := C.anchor_total
  suffix_nonflat := C.suffix_nonflat
  ancestor := ancestor G leader h m
  ancestor_visible := ancestor_visible_of_parent_visible G leader h m C.anchor_le_final visible C.parent_visible
  descendants_nonempty := descendants_nonempty_of_children G leader h m C.anchor_le_final visible C.children_nonempty
  descendants_mass := fun u _ => descendants_mass_le G leader h m C.anchor_le_final (visible m) u
  suffix_audit := C.suffix_audit

include C in
/-- A candidate passing these structural, flow, normalization and suffix
audits on a concrete strongly connected execution equals its population. -/
theorem accepted_candidate_eq_population
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    m = Fintype.card V :=
  (C.toAuditedCore connected).accepted_candidate_eq_population

end Checks

/-- Backward sums of a nonempty family preserve strict positivity. -/
theorem candidate_positive_of_anchor (h : ℕ)
    (visible : ∀ r, Finset (Node G leader r)) (candidate : ∀ r, Node G leader r → ℕ)
    (anchor : ∀ i ∈ visible h, 0 < candidate h i)
    (children : ∀ r, r < h → ∀ u ∈ visible r,
      ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty)
    (backward : ∀ r, r < h → ∀ u ∈ visible r,
      (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
        candidate r u) :
    ∀ r, r ≤ h → ∀ i ∈ visible r, 0 < candidate r i := by
  intro r hr
  apply Nat.decreasingInduction (motive := fun r _ => ∀ i ∈ visible r, 0 < candidate r i) ?_ anchor hr
  intro k hk ih u hu
  rw [← backward k hk u hu]
  exact Finset.sum_pos (fun i hi => ih i (Finset.mem_filter.mp hi).1) (children k hk u hu)

/-- Candidate leader mass is conserved by backward propagation because
input labels are inherited by actual history-tree children. -/
theorem leader_candidate_total_step (r : ℕ)
    (visible : ∀ r, Finset (Node G leader r)) (candidate : ∀ r, Node G leader r → ℕ)
    (maps : ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r)
    (backward : ∀ u ∈ visible r,
      (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
        candidate r u) :
    (∑ u ∈ visible r ∩ Finset.univ.filter (fun c => label G leader r c = true), candidate r u) =
    ∑ i ∈ visible (r + 1) ∩ Finset.univ.filter (fun c => label G leader (r + 1) c = true),
      candidate (r + 1) i := by
  let oldLeaders := visible r ∩ Finset.univ.filter (fun c => label G leader r c = true)
  let newLeaders := visible (r + 1) ∩ Finset.univ.filter (fun c => label G leader (r + 1) c = true)
  have leaderMaps : ∀ i ∈ newLeaders, parent G leader r i ∈ oldLeaders := by
    intro i hi
    obtain ⟨hivis, hil⟩ := Finset.mem_inter.mp hi
    refine Finset.mem_inter.mpr ⟨maps i hivis, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [label_parent]
    exact (Finset.mem_filter.mp hil).2
  have sameChildren : ∀ u ∈ oldLeaders,
      newLeaders.filter (fun i => parent G leader r i = u) =
      (visible (r + 1)).filter (fun i => parent G leader r i = u) := by
    intro u hu
    have hul : label G leader r u = true := (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2
    ext i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_filter.mp hi).1).1,
        (Finset.mem_filter.mp hi).2⟩
    · intro hi
      obtain ⟨hivis, hip⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hivis, ?_⟩, hip⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← label_parent, hip, hul]
  change (∑ u ∈ oldLeaders, candidate r u) = ∑ i ∈ newLeaders, candidate (r + 1) i
  calc
    (∑ u ∈ oldLeaders, candidate r u) = ∑ u ∈ oldLeaders,
        ∑ i ∈ newLeaders.filter (fun i => parent G leader r i = u), candidate (r + 1) i := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [sameChildren u hu, backward u (Finset.mem_inter.mp hu).1]
    _ = ∑ i ∈ newLeaders, candidate (r + 1) i := Finset.sum_fiberwise_of_maps_to leaderMaps _

/-- A normalized anchor normalizes every earlier visible leader sublevel. -/
theorem leader_candidate_of_anchor (h ell : ℕ)
    (visible : ∀ r, Finset (Node G leader r)) (candidate : ∀ r, Node G leader r → ℕ)
    (anchor : (∑ i ∈ visible h ∩ Finset.univ.filter (fun c => label G leader h c = true),
      candidate h i) = ell)
    (maps : ∀ r, r < h → ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r)
    (backward : ∀ r, r < h → ∀ u ∈ visible r,
      (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
        candidate r u) :
    ∀ r, r ≤ h → (∑ i ∈ visible r ∩ Finset.univ.filter (fun c => label G leader r c = true),
      candidate r i) = ell := by
  intro r hr
  apply Nat.decreasingInduction (motive := fun r _ =>
    (∑ i ∈ visible r ∩ Finset.univ.filter (fun c => label G leader r c = true), candidate r i) = ell)
    ?_ anchor hr
  intro k hk ih
  exact (leader_candidate_total_step G leader k visible candidate (maps k hk) (backward k hk)).trans ih

/-- The paper-facing audit interface checks positivity and leader
normalization only at the anchor, as Steps 3--4 specify. -/
structure PaperChecks (m h : ℕ)
    (visible : ∀ r, Finset (Node G leader r))
    (candidate : ∀ r, Node G leader r → ℕ) where
  anchor_positive : 1 ≤ h
  anchor_le_final : h ≤ m
  leaders_positive : 0 < FlatHistory.leaderCount leader
  anchor_candidate_positive : ∀ i ∈ visible h, 0 < candidate h i
  anchor_leader_candidate :
    (∑ i ∈ visible h ∩ Finset.univ.filter (fun c => label G leader h c = true), candidate h i) =
      FlatHistory.leaderCount leader
  parent_visible : ∀ r, r < m → ∀ i ∈ visible (r + 1), parent G leader r i ∈ visible r
  children_nonempty : ∀ r, r < m → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty
  backward : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ (visible (r + 1)).filter (fun i => parent G leader r i = u), candidate (r + 1) i) =
      candidate r u
  candidate_flow : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1),
      if parent G leader r i = u then outdegreeLabel G leader r i * candidate (r + 1) i else 0) =
    ∑ i ∈ visible (r + 1), redMultiplicity G leader r u i * candidate (r + 1) i
  anchor_total : (∑ i ∈ visible h, candidate h i) = m
  suffix_nonflat : ∀ r, h ≤ r → r < m →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => parent G leader r i = u)).card = 1
  suffix_audit : ∀ u ∈ visible h,
    ((visible m).filter (fun i => ancestor G leader h m i = u)).card ≤ candidate h u

namespace PaperChecks

variable {G leader} {m h : ℕ}
  {visible : ∀ r, Finset (Node G leader r)} {candidate : ∀ r, Node G leader r → ℕ}
  (C : PaperChecks G leader m h visible candidate)

include C in
/-- Both apparently stronger prefix premises are derived from the anchor. -/
theorem toChecks : Checks G leader m h visible candidate where
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  leaders_positive := C.leaders_positive
  candidate_positive := candidate_positive_of_anchor G leader h visible candidate C.anchor_candidate_positive
    (fun r hr => C.children_nonempty r (lt_of_lt_of_le hr C.anchor_le_final)) C.backward
  leader_candidate := leader_candidate_of_anchor G leader h (FlatHistory.leaderCount leader) visible candidate
    C.anchor_leader_candidate (fun r hr => C.parent_visible r (lt_of_lt_of_le hr C.anchor_le_final)) C.backward
  parent_visible := C.parent_visible
  children_nonempty := C.children_nonempty
  backward := C.backward
  candidate_flow := C.candidate_flow
  anchor_total := C.anchor_total
  suffix_nonflat := C.suffix_nonflat
  suffix_audit := C.suffix_audit

include C in
theorem accepted_candidate_eq_population
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    m = Fintype.card V := C.toChecks.accepted_candidate_eq_population connected

end PaperChecks
end Counting.CoreHistory
