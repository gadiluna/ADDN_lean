import Counting.TimingProtocolTransport

namespace Counting.TimingProtocolLocal
open DirectedCounting PaperHistory

def AnchorSolution (ell r : ℕ) (visible : ∀ r, Finset (FullHistory r))
    (z : FullHistory (r + 1) → ℚ) : Prop :=
  (∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1), (red r u i : ℚ) * z i) =
    ∑ i ∈ visible (r + 1), if parent r i = u then (degree r i : ℚ) * z i else 0) ∧
  (∑ i ∈ (visible (r + 1)).filter (fun c => input (r + 1) c = true), z i) = (ell : ℚ)

/-- All five paper steps, including the checks unnecessary for soundness:
the initial leader, level-size bounds, a flat last anchor, and uniqueness of
the exact rational anchor solution on its visible coordinates. -/
structure FullCertificate (ell m final r : ℕ) (visible : ∀ r, Finset (FullHistory r))
    (candidate : ∀ r, FullHistory r → ℕ)
    extends Certificate ell m final (r + 1) visible candidate where
  initial_leader : ∃ c ∈ visible 0, input 0 c = true
  node_bound : ∀ k, k ≤ final → (visible k).card ≤ m
  anchor_flat : ∀ u ∈ visible r, ((visible (r + 1)).filter (fun c => parent r c = u)).card = 1
  anchor_unique : ∀ z : FullHistory (r + 1) → ℚ, AnchorSolution ell r visible z →
    ∀ c ∈ visible (r + 1), z c = (candidate (r + 1) c : ℚ)

theorem FullCertificate.candidate_anchor_solution {ell m final r : ℕ}
    {visible : ∀ r, Finset (FullHistory r)} {candidate : ∀ r, FullHistory r → ℕ}
    (C : FullCertificate ell m final r visible candidate) :
    AnchorSolution ell r visible (fun c => (candidate (r + 1) c : ℚ)) := by
  constructor
  · intro u hu
    have flow := (C.candidate_flow r (Nat.lt_succ_self r) u hu).symm
    have rational := congrArg (fun n : ℕ => (n : ℚ)) flow
    simpa only [Nat.cast_sum, Nat.cast_mul, apply_ite, Nat.cast_zero] using rational
  · simpa only [Nat.cast_sum] using
      congrArg (fun n : ℕ => (n : ℚ)) C.anchor_leader_candidate

/-- Uniqueness is accompanied by an actual rational solution, so the
anchor test cannot succeed through a vacuous universal condition. -/
theorem FullCertificate.anchor_exists_unique_coordinates {ell m final r : ℕ}
    {visible : ∀ r, Finset (FullHistory r)} {candidate : ∀ r, FullHistory r → ℕ}
    (C : FullCertificate ell m final r visible candidate) :
    ∃ z, AnchorSolution ell r visible z ∧
      ∀ w, AnchorSolution ell r visible w → ∀ c ∈ visible (r + 1), w c = z c :=
  ⟨_, C.candidate_anchor_solution, C.anchor_unique⟩

def Pass (ell m final t : ℕ) (H : FullHistory t) : Prop :=
  ∃ r candidate, Nonempty (FullCertificate ell m final r (levels t H) candidate)

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

theorem fullCertificate_of_exhaustive {ell m final r t : ℕ} (observer : V)
    (valid : Admissible ell G leader)
    (population : m = Fintype.card V) (within : final ≤ t)
    (C : Concrete G leader m final (r + 1) (CoreTiming.levelsAt G leader t observer) (anonymity G leader))
    (exhaustive : ∀ k, k ≤ final → CoreTiming.levelsAt G leader t observer k = Finset.univ)
    (flat : FlatHistory.Flat G leader r) :
    FullCertificate ell m final r (levels t (history G leader t observer))
      (Concrete.extendCandidate (anonymity G leader)) := by
  classical
  letI : Nonempty V := ⟨observer⟩
  have count : FlatHistory.leaderCount leader = ell := valid.leaders
  have anchorBound := C.anchor_le_final
  have images : ∀ k, k ≤ final → levels t (history G leader t observer) k =
      Finset.univ.image (nodeHistory G leader k) := by
    intro k hk
    rw [levels_eq_image G leader t k (by omega) observer, exhaustive k hk]
  have localCert := C.toLocal count _ (fun k hk => levels_eq_image G leader t k (by omega) observer)
  refine { toCertificate := localCert, initial_leader := ?_, node_bound := ?_, anchor_flat := ?_, anchor_unique := ?_ }
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp C.leader_positive
    have hleader : leader v = true := (Finset.mem_filter.mp hv).2
    refine ⟨nodeHistory G leader 0 (classOf G leader 0 v), ?_, ?_⟩
    · rw [images 0 (by omega)]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · simpa only [nodeHistory_input, label_classOf] using hleader
  · intro k hk
    rw [images k hk, Finset.card_image_of_injective _ (nodeHistory_injective G leader k), Finset.card_univ, population]
    exact CoreCompleteness.card_level_le_population G leader k
  · intro H hH
    rw [images r (by omega)] at hH
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hH
    rw [images (r + 1) anchorBound, image_children,
      Finset.card_image_of_injective _ (nodeHistory_injective G leader (r + 1))]
    exact (CoreCompleteness.flat_iff_child_card_one G leader r).mp flat u
  · intro z ⟨flow, normalized⟩ H hH
    let actualZ : Node G leader (r + 1) → ℚ := fun c => z (nodeHistory G leader (r + 1) c)
    have actualFlow : FlatLevel.Flow (fun i j => (FlatHistory.weight G leader r i j : ℚ))
        (fun i => (outdegreeLabel G leader r i : ℚ)) actualZ := by
      intro i
      have hu : nodeHistory G leader r (PaperHistory.parent G leader r i) ∈
          levels t (history G leader t observer) r := by
        rw [images r (by omega)]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      have eq := flow _ hu
      rw [images (r + 1) anchorBound, sum_image_history, sum_image_history] at eq
      simpa only [nodeHistory_red, nodeHistory_parent, nodeHistory_degree,
        (nodeHistory_injective G leader r).eq_iff, flat.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        FlatLevel.Flow, FlatHistory.weight, actualZ]
        using eq
    have actualNormalized : (∑ i ∈ FlatHistory.leaders G leader r, actualZ i) =
        (FlatHistory.leaderCount leader : ℚ) := by
      rw [images (r + 1) anchorBound, image_leaders, Finset.univ_inter, sum_image_history] at normalized
      exact normalized.trans (congrArg (fun n : ℕ => (n : ℚ)) count.symm)
    have unique := FlatHistory.flat_level_anonymities_unique G leader r flat
      (valid.connected (r + 1) (by omega)) C.leader_positive actualZ actualFlow actualNormalized
    rw [images (r + 1) anchorBound] at hH
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hH
    rw [Concrete.extendCandidate_node]
    exact congrFun unique c

theorem core_pass_sound (ell m t : ℕ) (observer : V) (valid : Admissible ell G leader)
    (within : m ≤ t) :
    Pass ell m m t (history G leader t observer) → m = Fintype.card V := by
  rintro ⟨r, candidate, ⟨C⟩⟩
  have actual := C.toCertificate.toConcrete (G := G) (leader := leader) valid.leaders
    (fun k hk => levels_eq_image G leader t k (by omega) observer)
  exact actual.toCore.accepted_candidate_eq_population valid.connected

theorem true_core_pass (ell : ℕ) (observer : V) (valid : Admissible ell G leader) :
    Pass ell (Fintype.card V) (Fintype.card V) (2 * Fintype.card V - 1)
      (history G leader (2 * Fintype.card V - 1) observer) := by
  have count : FlatHistory.leaderCount leader = ell := valid.leaders
  obtain ⟨h, flat, ⟨C⟩⟩ := CoreCompleteness.exists_true_candidate_checks G leader
    (by rw [count]; exact valid.positive) _ (CoreTiming.core_prefix_exhaustive G leader valid.connected observer)
  cases h with
  | zero => have := C.anchor_positive; omega
  | succ r =>
    have positive : 0 < Fintype.card V := lt_of_lt_of_le valid.positive valid.leaderCount_le_card
    refine ⟨r, Concrete.extendCandidate (anonymity G leader), ⟨?_⟩⟩
    exact fullCertificate_of_exhaustive G leader observer valid rfl (by omega)
      (Concrete.ofCore C) (CoreTiming.core_prefix_exhaustive G leader valid.connected observer)
      (by simpa only [Nat.add_sub_cancel] using flat)

theorem false_short_pass (ell m : ℕ) (observer : V) (valid : Admissible ell G leader)
    (leaders : 2 ≤ ell) (larger : ell < m) (small : m < Fintype.card V) :
    ¬ Pass ell m (m - 1) (2 * m - 2) (history G leader (2 * m - 2) observer) := by
  rintro ⟨r, candidate, ⟨C⟩⟩
  have actual := C.toCertificate.toConcrete (G := G) (leader := leader) valid.leaders
    (fun k hk => levels_eq_image G leader (2 * m - 2) k (by omega) observer)
  exact actual.toShort.false_candidate_impossible small (by rw [show FlatHistory.leaderCount leader = ell from valid.leaders]; exact leaders)
    valid.connected

theorem true_short_pass (ell : ℕ) (observer : V) (valid : Admissible ell G leader)
    (nonleaders : ell < Fintype.card V) :
    Pass ell (Fintype.card V) (Fintype.card V - 1) (2 * Fintype.card V - 2)
      (history G leader (2 * Fintype.card V - 2) observer) := by
  have count : FlatHistory.leaderCount leader = ell := valid.leaders
  obtain ⟨h, flat, ⟨C⟩⟩ := ShortAudit.exists_true_short_checks G leader
    (by rw [count]; exact valid.positive) (by rwa [count]) _
    (ShortAudit.short_prefix_exhaustive G leader valid.connected observer)
  cases h with
  | zero => have := C.anchor_positive; omega
  | succ r =>
    refine ⟨r, Concrete.extendCandidate (anonymity G leader), ⟨?_⟩⟩
    exact fullCertificate_of_exhaustive G leader observer valid rfl (by omega)
      (Concrete.ofShort C) (ShortAudit.short_prefix_exhaustive G leader valid.connected observer)
      (by simpa only [Nat.add_sub_cancel] using flat)

end Counting.TimingProtocolLocal
