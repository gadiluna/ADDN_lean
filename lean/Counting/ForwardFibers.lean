import Counting.FlatHistory

/-!
# Fibers inside a proper subset

The concrete history-tree proof of Lemma `lem:forward-fibers`. The counted
objects are full nonleader history fibers contained in a fixed agent set.
Strong connectivity and the no-escape hypothesis create a newly contained
fiber at every round, independently of any candidate certificate.
-/

namespace Counting.ForwardFibers

open DirectedCounting DirectedCounting.PaperHistory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

noncomputable def insideNodes (S : Finset V) (r : ℕ) : Finset (Node G leader r) := by
  classical
  exact Finset.univ.filter (fun c => fiber G leader r c ⊆ S)

noncomputable def insideAgents (S : Finset V) (r : ℕ) : Finset V :=
  (insideNodes G leader S r).biUnion (fiber G leader r)

noncomputable def nonleaderInside (S : Finset V) (r : ℕ) : Finset (Node G leader r) := by
  classical
  exact Finset.univ.filter (fun c => label G leader r c = false ∧ fiber G leader r c ⊆ S)

theorem mem_insideNodes (S : Finset V) (r : ℕ) (c : Node G leader r) :
    c ∈ insideNodes G leader S r ↔ fiber G leader r c ⊆ S := by
  simp [insideNodes]

theorem mem_nonleaderInside (S : Finset V) (r : ℕ) (c : Node G leader r) :
    c ∈ nonleaderInside G leader S r ↔ label G leader r c = false ∧ fiber G leader r c ⊆ S := by
  simp [nonleaderInside]

theorem mem_insideAgents_iff (S : Finset V) (r : ℕ) (v : V) :
    v ∈ insideAgents G leader S r ↔ fiber G leader r (classOf G leader r v) ⊆ S := by
  constructor
  · intro hv
    obtain ⟨c, hc, hvc⟩ := Finset.mem_biUnion.mp hv
    have heq := (mem_fiber G leader r c v).mp hvc
    simpa only [heq] using (mem_insideNodes G leader S r c).mp hc
  · intro hsubset
    exact Finset.mem_biUnion.mpr ⟨classOf G leader r v,
      (mem_insideNodes G leader S r _).mpr hsubset, by simp⟩

theorem insideAgents_subset (S : Finset V) (r : ℕ) : insideAgents G leader S r ⊆ S := by
  intro v hv
  exact (mem_insideAgents_iff G leader S r v).mp hv (by simp)

omit [DecidableEq V] in
theorem leader_fiber_inside (S : Finset V)
    (allLeaders : ∀ v, leader v = true → v ∈ S) (r : ℕ) (v : V) (hv : leader v = true) :
    fiber G leader r (classOf G leader r v) ⊆ S := by
  intro w hw
  have hvfiber : v ∈ fiber G leader r (classOf G leader r v) := by simp
  have heq : leader w = leader v :=
    input_eq_of_mem_fiber G leader r (classOf G leader r v) hw hvfiber
  exact allLeaders w (heq.trans hv)

/-- At level zero, a proper set containing every leader cannot contain the
entire nonleader input class. -/
theorem nonleaderInside_zero (S : Finset V) (proper : S ≠ Finset.univ)
    (allLeaders : ∀ v, leader v = true → v ∈ S) : nonleaderInside G leader S 0 = ∅ := by
  classical
  have hmissing : ∃ v, v ∉ S := by
    by_contra h
    push Not at h
    exact proper (Finset.eq_univ_of_forall h)
  obtain ⟨v, hv⟩ := hmissing
  have hvfalse : leader v = false := Bool.eq_false_of_not_eq_true (fun hl => hv (allLeaders v hl))
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hcfalse, hcinside⟩ := (mem_nonleaderInside G leader S 0 c).mp hc
  have hclass : classOf G leader 0 v = c := by
    calc
      classOf G leader 0 v = classOf G leader 0 c.out := by
        apply (classOf_eq_iff G leader 0 v c.out).mpr
        change leader v = leader c.out
        exact hvfalse.trans hcfalse.symm
      _ = c := classOf_out G leader 0 c
  exact hv (hcinside ((mem_fiber G leader 0 c v).mpr hclass))

/-- Each counted node consumes at least one of the nonleaders in S. -/
theorem nonleaderInside_card_bound (S : Finset V)
    (allLeaders : ∀ v, leader v = true → v ∈ S) (r : ℕ) :
    (nonleaderInside G leader S r).card ≤ S.card - FlatHistory.leaderCount leader := by
  classical
  have hleaderSet : S.filter (fun v => leader v = true) = Finset.univ.filter (fun v => leader v = true) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨allLeaders v h, h⟩⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun v => leader v = true)
  simp only [Bool.not_eq_true] at hsplit
  rw [hleaderSet] at hsplit
  change FlatHistory.leaderCount leader + (S.filter (fun v => leader v = false)).card = S.card at hsplit
  have hcount : (nonleaderInside G leader S r).card ≤
      (S.filter (fun v => leader v = false)).card := by
    calc
      (nonleaderInside G leader S r).card = ∑ _ ∈ nonleaderInside G leader S r, 1 := by simp
      _ ≤ ∑ c ∈ nonleaderInside G leader S r, anonymity G leader r c :=
        Finset.sum_le_sum (fun c _ => anonymity_pos G leader r c)
      _ = (Finset.univ.filter (fun v => classOf G leader r v ∈ nonleaderInside G leader S r)).card :=
        sum_anonymity_eq_card_filter G leader r _
      _ ≤ (S.filter (fun v => leader v = false)).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨hlabel, hinside⟩ := (mem_nonleaderInside G leader S r _).mp (Finset.mem_filter.mp hv).2
        exact Finset.mem_filter.mpr ⟨hinside (by simp), by simpa only [label_classOf] using hlabel⟩
  omega

/-- No edge leaves S from any previous full fiber that is wholly in S. -/
def NoEscape (S : Finset V) (r : ℕ) : Prop :=
  ∀ c : Node G leader r, fiber G leader r c ⊆ S →
    ∀ a ∈ fiber G leader r c, ∀ b, b ∉ S → G (r + 1) a b = 0

/-- The outgoing cut supplies a new nonleader fiber contained in S whose
parent was not already contained in S. -/
theorem exists_new_nonleader_fiber (S : Finset V) (proper : S ≠ Finset.univ)
    (allLeaders : ∀ v, leader v = true → v ∈ S)
    (positiveLeaders : 0 < FlatHistory.leaderCount leader) (r : ℕ)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v)) (noEscape : NoEscape G leader S r) :
    ∃ c ∈ nonleaderInside G leader S (r + 1), parent G leader r c ∉ nonleaderInside G leader S r := by
  classical
  let T := insideAgents G leader S r
  have hTnonempty : T.Nonempty := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp positiveLeaders
    have hl := (Finset.mem_filter.mp hv).2
    exact ⟨v, (mem_insideAgents_iff G leader S r v).mpr (leader_fiber_inside G leader S allLeaders r v hl)⟩
  have hTproper : ∃ v, v ∉ T := by
    by_contra h
    push Not at h
    apply proper
    apply Finset.eq_univ_of_forall
    intro v
    exact insideAgents_subset G leader S r (h v)
  obtain ⟨a, b, ha, hb, hab⟩ := exists_edge_leaving connected
    (Q := (T : Set V)) hTnonempty hTproper
  let A := fiber G leader r (classOf G leader r a)
  have hAinside : A ⊆ S := (mem_insideAgents_iff G leader S r a).mp ha
  have haA : a ∈ A := by simp [A]
  have hreceived : 0 < weightedIncomingCount (G (r + 1)) A b := by
    exact lt_of_lt_of_le hab
      (Finset.single_le_sum (f := fun v => G (r + 1) v b) (fun _ _ => Nat.zero_le _) haA)
  have hnewInside : fiber G leader (r + 1) (classOf G leader (r + 1) b) ⊆ S := by
    intro x hx
    by_contra hxS
    have hzero : weightedIncomingCount (G (r + 1)) A x = 0 := by
      unfold weightedIncomingCount
      apply Finset.sum_eq_zero
      intro v hv
      exact noEscape (classOf G leader r a) hAinside v hv x hxS
    have heq : weightedIncomingCount (G (r + 1)) A x = weightedIncomingCount (G (r + 1)) A b := by
      change weightedIncomingCount (G (r + 1)) (fiber G leader r (classOf G leader r a)) x =
        weightedIncomingCount (G (r + 1)) (fiber G leader r (classOf G leader r a)) b
      rw [incoming_eq_redMultiplicity G leader r _ _ hx,
        incoming_eq_redMultiplicity G leader r _ _ (show b ∈ fiber G leader (r + 1) (classOf G leader (r + 1) b) by simp)]
    omega
  have hbfalse : leader b = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hleader
    exact hb ((mem_insideAgents_iff G leader S r b).mpr (leader_fiber_inside G leader S allLeaders r b hleader))
  refine ⟨classOf G leader (r + 1) b, ?_, ?_⟩
  · apply (mem_nonleaderInside G leader S (r + 1) _).mpr
    exact ⟨by simpa only [label_classOf] using hbfalse, hnewInside⟩
  · intro hparent
    rw [parent_classOf] at hparent
    have hsubset := ((mem_nonleaderInside G leader S r _).mp hparent).2
    exact hb ((mem_insideAgents_iff G leader S r b).mpr hsubset)

/-- Every old counted fiber has a counted child. -/
theorem nonleaderInside_subset_parent_image (S : Finset V) (r : ℕ) :
    nonleaderInside G leader S r ⊆
      (nonleaderInside G leader S (r + 1)).image (parent G leader r) := by
  intro u hu
  obtain ⟨hlabel, hinside⟩ := (mem_nonleaderInside G leader S r u).mp hu
  obtain ⟨c, hc⟩ := forgetMultigraphHistoryClass_surjective G leader r u
  change parent G leader r c = u at hc
  refine Finset.mem_image.mpr ⟨c, ?_, hc⟩
  apply (mem_nonleaderInside G leader S (r + 1) c).mpr
  constructor
  · rw [← label_parent, hc]
    exact hlabel
  · have hsubset := fiber_subset_parent G leader r c
    rw [hc] at hsubset
    exact hsubset.trans hinside

theorem nonleaderInside_strict_growth (S : Finset V) (proper : S ≠ Finset.univ)
    (allLeaders : ∀ v, leader v = true → v ∈ S)
    (positiveLeaders : 0 < FlatHistory.leaderCount leader) (r : ℕ)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v)) (noEscape : NoEscape G leader S r) :
    (nonleaderInside G leader S r).card < (nonleaderInside G leader S (r + 1)).card := by
  obtain ⟨c, hc, hparent⟩ := exists_new_nonleader_fiber G leader S proper allLeaders positiveLeaders r connected noEscape
  have hstrict : nonleaderInside G leader S r ⊂
      (nonleaderInside G leader S (r + 1)).image (parent G leader r) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨nonleaderInside_subset_parent_image G leader S r, ?_⟩
    intro heq
    apply hparent
    rw [heq]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  exact lt_of_lt_of_le (Finset.card_lt_card hstrict) (Finset.card_image_le)

/-- The paper's Fibers inside a proper subset lemma. The old-level index
`r < h` corresponds to round `r+1`, covering manuscript rounds `1,...,h`. -/
theorem fibers_inside_proper_subset (S : Finset V) (h ell : ℕ)
    (proper : S ≠ Finset.univ) (allLeaders : ∀ v, leader v = true → v ∈ S)
    (leaderCount : FlatHistory.leaderCount leader = ell) (positiveLeaders : 0 < ell)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (noEscape : ∀ r, r < h → NoEscape G leader S r) : h ≤ S.card - ell := by
  have hpositive : 0 < FlatHistory.leaderCount leader := by omega
  have growth : ∀ r, r ≤ h →
      (nonleaderInside G leader S 0).card + r ≤ (nonleaderInside G leader S r).card := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hprior := ih (by omega)
      have hnext := nonleaderInside_strict_growth G leader S proper allLeaders hpositive r
        (connected (r + 1) (by omega)) (noEscape r (by omega))
      omega
  have lower := growth h le_rfl
  rw [nonleaderInside_zero G leader S proper allLeaders, Finset.card_empty, zero_add] at lower
  have upper := nonleaderInside_card_bound G leader S allLeaders h
  rw [leaderCount] at upper
  exact lower.trans upper

end Counting.ForwardFibers
