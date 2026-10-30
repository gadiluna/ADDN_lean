import Counting.InputMultisetLocal
import Counting.InputMultisetRecovery
import Counting.HistoryBridge

/-! The executable local history levels are exactly the observed quotient
classes. All complete-prefix premises are derived from dynamic connectivity. -/

namespace Counting.InputMultisetLocal
open DirectedCounting DirectedCounting.PaperHistory
open scoped BigOperators

/-- Exact equivalence with the paper's recursive class-count definition. -/
theorem history_eq_iff_sameMultigraphHistory {V Input : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (t : Nat) (x y : V) :
    InputProtocol.history G leader input t x = InputProtocol.history G leader input t y ↔
      sameMultigraphHistory G (fun v => (leader v, input v)) t x y := by
  classical
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
      change (_ = _) ↔ (_ ∧ _ ∧ _)
      constructor
      · intro heq
        have hp := congrArg Prod.fst heq
        have hd := congrArg (fun h : InputProtocol.FullHistory Input (t + 1) => h.2.1) heq
        have hm := congrArg (fun h : InputProtocol.FullHistory Input (t + 1) => h.2.2) heq
        refine ⟨(ih x y).mp hp, hd, ?_⟩
        intro z
        have hc := congrArg (Multiset.count (InputProtocol.history G leader input t z)) hm
        simp only [InputProtocol.history, count_incoming] at hc
        simpa only [weightedIncomingFromClass, ← ih] using hc
      · rintro ⟨hp, hd, hm⟩
        apply Prod.ext ((ih x y).mpr hp)
        apply Prod.ext hd
        apply Multiset.ext.mpr
        intro a
        simp only [InputProtocol.history, count_incoming]
        by_cases ha : ∃ z, InputProtocol.history G leader input t z = a
        · obtain ⟨z, rfl⟩ := ha
          simpa only [weightedIncomingFromClass, ← ih] using hm z
        · have hnone : ∀ z, InputProtocol.history G leader input t z ≠ a := by simpa using ha
          simp [hnone]


variable {V Input : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input)

noncomputable def nodeHistory (r : Nat)
    (c : Node G (fun v => (leader v, input v)) r) : InputProtocol.FullHistory Input r :=
  InputProtocol.history G leader input r c.out

@[simp] theorem nodeHistory_classOf (r : Nat) (v : V) :
    nodeHistory G leader input r (classOf G (fun v => (leader v, input v)) r v) =
      InputProtocol.history G leader input r v := by
  apply (history_eq_iff_sameMultigraphHistory G leader input r _ _).mpr
  exact (classOf_eq_iff G _ r _ _).mp (classOf_out G _ r _)

theorem nodeHistory_injective (r : Nat) : Function.Injective (nodeHistory G leader input r) := by
  intro c d heq
  have same := (history_eq_iff_sameMultigraphHistory G leader input r c.out d.out).mp heq
  simpa only [classOf_out] using (classOf_eq_iff G _ r c.out d.out).mpr same

@[simp] theorem nodeHistory_initial (r : Nat)
    (c : Node G (fun v => (leader v, input v)) r) :
    InputProtocol.FullHistory.initial r (nodeHistory G leader input r c) =
      label G (fun v => (leader v, input v)) r c := by
  exact InputProtocol.initial_history G leader input r c.out

@[simp] theorem nodeHistory_parent (r : Nat)
    (c : Node G (fun v => (leader v, input v)) (r + 1)) :
    (nodeHistory G leader input (r + 1) c).1 =
      nodeHistory G leader input r (PaperHistory.parent G (fun v => (leader v, input v)) r c) := by
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective c
  change (nodeHistory G leader input (r + 1) (classOf G _ (r + 1) v)).1 =
    nodeHistory G leader input r (PaperHistory.parent G _ r (classOf G _ (r + 1) v))
  simp only [nodeHistory_classOf, parent_classOf]
  rfl

@[simp] theorem nodeHistory_degree (r : Nat)
    (c : Node G (fun v => (leader v, input v)) (r + 1)) :
    (nodeHistory G leader input (r + 1) c).2.1 =
      outdegreeLabel G (fun v => (leader v, input v)) r c := rfl

variable [DecidableEq Input]

@[simp] theorem nodeHistory_red (r : Nat)
    (p : Node G (fun v => (leader v, input v)) r)
    (c : Node G (fun v => (leader v, input v)) (r + 1)) :
    (nodeHistory G leader input (r + 1) c).2.2.count (nodeHistory G leader input r p) =
      redMultiplicity G (fun v => (leader v, input v)) r p c := by
  classical
  change (incoming (G (r + 1)) (InputProtocol.history G leader input r) c.out).count
    (nodeHistory G leader input r p) = _
  rw [count_incoming]
  unfold redMultiplicity weightedIncomingCount fiber
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  have heq : InputProtocol.history G leader input r v = nodeHistory G leader input r p ↔
      classOf G (fun v => (leader v, input v)) r v = p := by
    rw [← nodeHistory_classOf]
    exact (nodeHistory_injective G leader input r).eq_iff
  simp only [heq]

omit [DecidableEq Input] in
theorem cast_history (a b : Nat) (heq : a = b) (v : V) :
    cast (congrArg (InputProtocol.FullHistory Input) heq)
      (InputProtocol.history G leader input a v) = InputProtocol.history G leader input b v := by
  cases heq
  rfl

/-- Occurrence in a local history is exactly causal visibility from some agent. -/
theorem mem_occurrences_iff_causal (r d : Nat) (x : V)
    (h : InputProtocol.FullHistory Input r) :
    h ∈ occurrences r d (InputProtocol.history G leader input (r + d) x) ↔
      ∃ y, h = InputProtocol.history G leader input r y ∧
        TemporalReach (fun t u v => 0 < G t u v) r y d x := by
  induction d generalizing x with
  | zero =>
    simp only [occurrences, Finset.mem_singleton]
    constructor
    · intro hh
      exact ⟨x, hh, TemporalReach.zero⟩
    · rintro ⟨y, hh, hr⟩
      cases hr
      exact hh
  | succ d ih =>
    simp only [occurrences, InputProtocol.history, Finset.mem_union, Finset.mem_biUnion,
      Multiset.mem_toFinset]
    constructor
    · rintro (hold | ⟨z, hz, hseen⟩)
      · obtain ⟨y, hy, hp⟩ := (ih x).mp hold
        exact ⟨y, hy, TemporalReach.stay hp⟩
      · obtain ⟨v, hedge, hv⟩ := (mem_incoming _ _ _ _).mp hz
        rw [← hv] at hseen
        obtain ⟨y, hy, hp⟩ := (ih v).mp hseen
        exact ⟨y, hy, TemporalReach.send hp hedge⟩
    · rintro ⟨y, hy, hp⟩
      rcases (temporalReach_succ_iff _ _ _ _ _).mp hp with hold | ⟨v, hpv, hedge⟩
      · exact Or.inl ((ih x).mpr ⟨y, hy, hold⟩)
      · exact Or.inr ⟨InputProtocol.history G leader input (r + d) v,
          (mem_incoming _ _ _ _).mpr ⟨v, hedge, rfl⟩,
          (ih v).mpr ⟨y, hy, hpv⟩⟩

/-- After `n - 1` communication rounds every earlier history is visible. -/
theorem mem_occurrences_after_delay
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (r d : Nat) (delay : Fintype.card V - 1 ≤ d) (source observer : V) :
    InputProtocol.history G leader input r source ∈
      occurrences r d (InputProtocol.history G leader input (r + d) observer) := by
  apply (mem_occurrences_iff_causal G leader input r d observer _).mpr
  refine ⟨source, rfl, ?_⟩
  have h := temporalReach_after_card_sub_one (fun t u v => 0 < G t u v)
    connected r source observer
  induction d, delay using Nat.le_induction with
  | base => exact h
  | succ d hd ih => exact TemporalReach.stay ih

/-- At sufficient depth an executable local level contains every quotient
history, with neither extra nor missing histories. -/
theorem levels_full
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (t r : Nat) (delay : r + (Fintype.card V - 1) ≤ t) (observer : V) :
    levels t (InputProtocol.history G leader input t observer) r =
      Finset.univ.image (nodeHistory G leader input r) := by
  have within : r ≤ t := by omega
  unfold levels
  rw [dif_pos within, cast_history G leader input t (r + (t - r))
    (Nat.add_sub_of_le within).symm observer]
  ext H
  constructor
  · intro hH
    obtain ⟨v, hv, _⟩ := (mem_occurrences_iff_causal G leader input r (t - r) observer H).mp hH
    exact Finset.mem_image.mpr ⟨classOf G _ r v, Finset.mem_univ _,
      (nodeHistory_classOf G leader input r v).trans hv.symm⟩
  · intro hH
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hH
    exact mem_occurrences_after_delay G leader input connected r (t - r) (by omega) c.out observer

omit [DecidableEq Input] in
/-- Forgetting the leader coordinate in the recovered labelled multiset
gives precisely the multiset of private inputs. -/
theorem true_multiset (r : Nat) :
    (∑ c : Node G (fun v => (leader v, input v)) r,
      Multiset.replicate (anonymity G (fun v => (leader v, input v)) r c)
        (label G (fun v => (leader v, input v)) r c).2) =
      (Finset.univ : Finset V).val.map input := by
  have sum_map : ∀ (s : Finset (Node G (fun v => (leader v, input v)) r)),
      (∑ c ∈ s, Multiset.replicate (anonymity G (fun v => (leader v, input v)) r c)
        (label G (fun v => (leader v, input v)) r c)).map Prod.snd =
      ∑ c ∈ s, Multiset.replicate (anonymity G (fun v => (leader v, input v)) r c)
        (label G (fun v => (leader v, input v)) r c).2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
      simp [Finset.sum_insert, hc, Multiset.map_add, Multiset.map_replicate, ih]
  rw [← sum_map]
  change (InputMultisetRecovery.weightedMultiset G (fun v => (leader v, input v)) r
    (anonymity G (fun v => (leader v, input v)) r)).map Prod.snd = _
  rw [InputMultisetRecovery.weighted_multiset_eq]
  simp [InputMultisetRecovery.populationMultiset, Multiset.map_map]

end Counting.InputMultisetLocal
