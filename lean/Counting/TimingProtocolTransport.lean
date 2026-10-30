import Counting.TimingProtocolLocal

namespace Counting.TimingProtocolLocal
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- An independently indexed final level unifies the core and short checks
without equating candidate population with prefix length. -/
structure Concrete (m final anchor : ℕ) (visible : ∀ r, Finset (Node G leader r))
    (candidate : ∀ r, Node G leader r → ℕ)
    extends CreditHistory.PrefixChecks G leader m anchor visible candidate where
  anchor_positive : 1 ≤ anchor
  anchor_le_final : anchor ≤ final
  all_parent_visible : ∀ r, r < final → ∀ i ∈ visible (r + 1), PaperHistory.parent G leader r i ∈ visible r
  all_children_nonempty : ∀ r, r < final → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => PaperHistory.parent G leader r i = u)).Nonempty
  suffix_nonflat : ∀ r, anchor ≤ r → r < final →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => PaperHistory.parent G leader r i = u)).card = 1
  suffix_audit : ∀ u ∈ visible anchor,
    ((visible final).filter (fun i => CoreHistory.ancestor G leader anchor final i = u)).card ≤ candidate anchor u

theorem image_children (r : ℕ) (nodes : Finset (Node G leader (r + 1))) (u : Node G leader r) :
    (nodes.image (nodeHistory G leader (r + 1))).filter (fun H => parent r H = nodeHistory G leader r u) =
      (nodes.filter (fun c => PaperHistory.parent G leader r c = u)).image (nodeHistory G leader (r + 1)) := by
  rw [Finset.filter_image]
  congr 1
  ext c
  simp only [Finset.mem_filter, nodeHistory_parent, (nodeHistory_injective G leader r).eq_iff]

theorem image_descendants (r t : ℕ) (hrt : r ≤ t) (nodes : Finset (Node G leader t)) (u : Node G leader r) :
    (nodes.image (nodeHistory G leader t)).filter (fun H => ancestor r t H = nodeHistory G leader r u) =
      (nodes.filter (fun c => CoreHistory.ancestor G leader r t c = u)).image (nodeHistory G leader t) := by
  rw [Finset.filter_image]
  congr 1
  ext c
  simp only [Finset.mem_filter, nodeHistory_ancestor G leader r t hrt, (nodeHistory_injective G leader r).eq_iff]

theorem image_leaders (r : ℕ) (nodes : Finset (Node G leader r)) :
    (nodes.image (nodeHistory G leader r)).filter (fun H => input r H = true) =
      (nodes ∩ Finset.univ.filter (fun c => label G leader r c = true)).image (nodeHistory G leader r) := by
  rw [Finset.filter_image]
  congr 1
  ext c
  simp only [Finset.mem_filter, nodeHistory_input, Finset.mem_inter, Finset.mem_univ, true_and]

theorem sum_image_history {M : Type*} [AddCommMonoid M]
    (r : ℕ) (nodes : Finset (Node G leader r)) (f : FullHistory r → M) :
    (∑ H ∈ nodes.image (nodeHistory G leader r), f H) = ∑ c ∈ nodes, f (nodeHistory G leader r c) :=
  Finset.sum_image (fun _ _ _ _ heq => nodeHistory_injective G leader r heq)

namespace Certificate
variable {G leader} {ell m final anchor : ℕ}
  {visible : ∀ r, Finset (Node G leader r)} {localVisible : ∀ r, Finset (FullHistory r)}
  {candidate : ∀ r, FullHistory r → ℕ}

/-- Transport is only over the audited prefix. Actual population, labels,
and multiplicities enter here solely in the proof. -/
theorem toConcrete (C : Certificate ell m final anchor localVisible candidate)
    (count : FlatHistory.leaderCount leader = ell)
    (images : ∀ r, r ≤ final → localVisible r = (visible r).image (nodeHistory G leader r)) :
    Concrete G leader m final anchor visible (fun r c => candidate r (nodeHistory G leader r c)) := by
  have memImage : ∀ r, r ≤ final → ∀ c,
      nodeHistory G leader r c ∈ localVisible r ↔ c ∈ visible r := by
    intro r hr c
    rw [images r hr]
    exact Finset.mem_image.trans ⟨fun ⟨d, hd, heq⟩ => nodeHistory_injective G leader r heq ▸ hd,
      fun hc => ⟨c, hc, rfl⟩⟩
  have sumEq : ∀ r, r ≤ final → ∀ f : FullHistory r → ℕ,
      (∑ H ∈ localVisible r, f H) = ∑ c ∈ visible r, f (nodeHistory G leader r c) := by
    intro r hr f
    rw [images r hr, sum_image_history]
  have childImage : ∀ r, r < final → ∀ u,
      (localVisible (r + 1)).filter (fun H => parent r H = nodeHistory G leader r u) =
        ((visible (r + 1)).filter (fun c => PaperHistory.parent G leader r c = u)).image (nodeHistory G leader (r + 1)) := by
    intro r hr u
    rw [images (r + 1) (by omega), image_children]
  have anchorBound := C.anchor_le_final
  refine {
    leader_positive := count ▸ C.leader_positive
    anchor_positive := C.anchor_positive
    anchor_le_final := C.anchor_le_final
    anchor_candidate_positive := fun c hc => C.anchor_candidate_positive _ ((memImage anchor C.anchor_le_final c).mpr hc)
    anchor_leader_candidate := ?_
    anchor_total := ?_
    parent_visible := ?_
    all_parent_visible := ?_
    children_nonempty := ?_
    all_children_nonempty := ?_
    backward := ?_
    candidate_flow := ?_
    suffix_nonflat := ?_
    suffix_audit := ?_ }
  · have normalized := C.anchor_leader_candidate
    rw [images anchor C.anchor_le_final, image_leaders, sum_image_history] at normalized
    exact normalized.trans count.symm
  · simpa only [sumEq anchor C.anchor_le_final] using C.anchor_total
  · intro r hr c hc
    apply (memImage r (by omega) _).mp
    rw [← nodeHistory_parent]
    exact C.parent_visible r (by omega) _ ((memImage (r + 1) (by omega) c).mpr hc)
  · intro r hr u hu
    have child := C.children_nonempty r (by omega) _ ((memImage r (by omega) u).mpr hu)
    rw [childImage r (by omega) u] at child
    exact Finset.image_nonempty.mp child
  · intro r hr u hu
    have back := C.backward r hr _ ((memImage r (by omega) u).mpr hu)
    rwa [childImage r (by omega) u, sum_image_history] at back
  · intro r hr u hu
    have flow := C.candidate_flow r hr _ ((memImage r (by omega) u).mpr hu)
    rw [sumEq (r + 1) (by omega), sumEq (r + 1) (by omega)] at flow
    simpa only [nodeHistory_parent, nodeHistory_degree, nodeHistory_red,
      (nodeHistory_injective G leader r).eq_iff] using flow
  · intro r hr c hc
    apply (memImage r (by omega) _).mp
    rw [← nodeHistory_parent]
    exact C.parent_visible r hr _ ((memImage (r + 1) (by omega) c).mpr hc)
  · intro r hr u hu
    have child := C.children_nonempty r hr _ ((memImage r (by omega) u).mpr hu)
    rw [childImage r hr u] at child
    exact Finset.image_nonempty.mp child
  · intro r hr hrf flat
    apply C.suffix_nonflat r hr hrf
    intro H hH
    rw [images r (by omega)] at hH
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hH
    rw [childImage r hrf u, Finset.card_image_of_injective _ (nodeHistory_injective G leader (r + 1))]
    exact flat u hu
  · intro u hu
    have audit := C.suffix_audit _ ((memImage anchor C.anchor_le_final u).mpr hu)
    rw [images final le_rfl, image_descendants G leader anchor final C.anchor_le_final,
      Finset.card_image_of_injective _ (nodeHistory_injective G leader final)] at audit
    exact audit

end Certificate

namespace Concrete
variable {G leader} {m final anchor : ℕ}
  {visible : ∀ r, Finset (Node G leader r)} {candidate : ∀ r, Node G leader r → ℕ}

/-- Extend a mathematical assignment to all possible histories. The
extension is used only as an existential certificate witness. -/
noncomputable def extendCandidate (candidate : ∀ r, Node G leader r → ℕ)
    (r : ℕ) (H : FullHistory r) : ℕ := by
  classical
  exact if realized : ∃ c, nodeHistory G leader r c = H then candidate r realized.choose else 0

@[simp] theorem extendCandidate_node (r : ℕ) (c : Node G leader r) :
    extendCandidate candidate r (nodeHistory G leader r c) = candidate r c := by
  classical
  unfold extendCandidate
  rw [dif_pos ⟨c, rfl⟩]
  congr 1
  exact nodeHistory_injective G leader r (Classical.choose_spec (show ∃ d, nodeHistory G leader r d = nodeHistory G leader r c from ⟨c, rfl⟩))

theorem toLocal (C : Concrete G leader m final anchor visible candidate)
    {ell : ℕ} (count : FlatHistory.leaderCount leader = ell)
    (localVisible : ∀ r, Finset (FullHistory r))
    (images : ∀ r, r ≤ final → localVisible r = (visible r).image (nodeHistory G leader r)) :
    Certificate ell m final anchor localVisible (extendCandidate candidate) := by
  have anchorBound := C.anchor_le_final
  have member : ∀ r, r ≤ final → ∀ c ∈ visible r, nodeHistory G leader r c ∈ localVisible r := by
    intro r hr c hc
    rw [images r hr]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have representative : ∀ r, r ≤ final → ∀ H ∈ localVisible r,
      ∃ c ∈ visible r, nodeHistory G leader r c = H := by
    intro r hr H hH
    rw [images r hr] at hH
    exact Finset.mem_image.mp hH
  have childImage : ∀ r, r < final → ∀ u,
      (localVisible (r + 1)).filter (fun H => parent r H = nodeHistory G leader r u) =
        ((visible (r + 1)).filter (fun c => PaperHistory.parent G leader r c = u)).image (nodeHistory G leader (r + 1)) := by
    intro r hr u
    rw [images (r + 1) (by omega), image_children]
  refine {
    leader_positive := count ▸ C.leader_positive
    anchor_positive := C.anchor_positive
    anchor_le_final := C.anchor_le_final
    anchor_candidate_positive := ?_
    anchor_leader_candidate := ?_
    anchor_total := ?_
    parent_visible := ?_
    children_nonempty := ?_
    backward := ?_
    candidate_flow := ?_
    suffix_nonflat := ?_
    suffix_audit := ?_ }
  · intro H hH
    obtain ⟨c, hc, rfl⟩ := representative anchor anchorBound H hH
    simpa only [extendCandidate_node] using C.anchor_candidate_positive c hc
  · rw [images anchor anchorBound, image_leaders, sum_image_history]
    simpa only [extendCandidate_node, count] using C.anchor_leader_candidate
  · rw [images anchor anchorBound, sum_image_history]
    simpa only [extendCandidate_node] using C.anchor_total
  · intro r hr H hH
    obtain ⟨c, hc, rfl⟩ := representative (r + 1) (by omega) H hH
    rw [nodeHistory_parent]
    exact member r (by omega) _ (C.all_parent_visible r hr c hc)
  · intro r hr H hH
    obtain ⟨c, hc, rfl⟩ := representative r (by omega) H hH
    rw [childImage r hr c]
    exact (C.all_children_nonempty r hr c hc).image _
  · intro r hr H hH
    obtain ⟨c, hc, rfl⟩ := representative r (by omega) H hH
    rw [childImage r (by omega) c, sum_image_history]
    simpa only [extendCandidate_node] using C.backward r hr c hc
  · intro r hr H hH
    obtain ⟨c, hc, rfl⟩ := representative r (by omega) H hH
    rw [images (r + 1) (by omega), sum_image_history, sum_image_history]
    simpa only [nodeHistory_parent, nodeHistory_degree, nodeHistory_red, extendCandidate_node,
      (nodeHistory_injective G leader r).eq_iff] using C.candidate_flow r hr c hc
  · intro r hr hrf flat
    apply C.suffix_nonflat r hr hrf
    intro c hc
    have one := flat _ (member r (by omega) c hc)
    rwa [childImage r hrf c, Finset.card_image_of_injective _ (nodeHistory_injective G leader (r + 1))] at one
  · intro H hH
    obtain ⟨c, hc, rfl⟩ := representative anchor anchorBound H hH
    rw [images final le_rfl, image_descendants G leader anchor final anchorBound,
      Finset.card_image_of_injective _ (nodeHistory_injective G leader final), extendCandidate_node]
    exact C.suffix_audit c hc

theorem toCore (C : Concrete G leader m m anchor visible candidate) :
    CoreHistory.PaperChecks G leader m anchor visible candidate where
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  leaders_positive := C.leader_positive
  anchor_candidate_positive := C.anchor_candidate_positive
  anchor_leader_candidate := C.anchor_leader_candidate
  parent_visible := C.all_parent_visible
  children_nonempty := C.all_children_nonempty
  backward := C.backward
  candidate_flow := C.candidate_flow
  anchor_total := C.anchor_total
  suffix_nonflat := C.suffix_nonflat
  suffix_audit := C.suffix_audit

theorem toShort (C : Concrete G leader m (m - 1) anchor visible candidate) :
    ShortAudit.Checks G leader m anchor visible candidate where
  toPrefixChecks := C.toPrefixChecks
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  all_parent_visible := C.all_parent_visible
  all_children_nonempty := C.all_children_nonempty
  suffix_nonflat := C.suffix_nonflat
  suffix_audit := C.suffix_audit

theorem ofCore (C : CoreHistory.Checks G leader m anchor visible candidate) :
    Concrete G leader m m anchor visible candidate where
  leader_positive := C.leaders_positive
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  anchor_candidate_positive := C.candidate_positive anchor le_rfl
  anchor_leader_candidate := C.leader_candidate anchor le_rfl
  anchor_total := C.anchor_total
  parent_visible := fun r hr => C.parent_visible r (lt_of_lt_of_le hr C.anchor_le_final)
  children_nonempty := fun r hr => C.children_nonempty r (lt_of_lt_of_le hr C.anchor_le_final)
  all_parent_visible := C.parent_visible
  all_children_nonempty := C.children_nonempty
  backward := C.backward
  candidate_flow := C.candidate_flow
  suffix_nonflat := C.suffix_nonflat
  suffix_audit := C.suffix_audit

theorem ofShort (C : ShortAudit.Checks G leader m anchor visible candidate) :
    Concrete G leader m (m - 1) anchor visible candidate where
  toPrefixChecks := C.toPrefixChecks
  anchor_positive := C.anchor_positive
  anchor_le_final := C.anchor_le_final
  all_parent_visible := C.all_parent_visible
  all_children_nonempty := C.all_children_nonempty
  suffix_nonflat := C.suffix_nonflat
  suffix_audit := C.suffix_audit

end Concrete
end Counting.TimingProtocolLocal
