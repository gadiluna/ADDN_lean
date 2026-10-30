import Counting.RealizabilityConstructionTransport
import Counting.RealizabilityConstructionRound

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal RealizabilityConstruction

variable {ell N t : Nat} {H : FullHistory t} {k : Counts}

structure RealizingRound (cert : Certificate ell N t H k) (r : Nat)
    (E : CountAllocation.Population N ell → CountAllocation.Population N ell → Nat) : Prop where
  connected : StronglyConnected (fun a b => 0 < E a b)
  degrees : ∀ a v, cert.tag (r + 1) a = some v → (∑ b, E a b) = degree r v.val
  receipts : ∀ a v, cert.tag (r + 1) a = some v → ∀ u,
    taggedIncoming E (cert.tag r) u a = red r u.val v.val
  exclude : ∀ a v, cert.tag (r + 1) a = some v → ∀ b, cert.tag r b = none → E b a = 0

theorem Certificate.round_exists (cert : Certificate ell N t H k) (r : Nat)
    (before : r < t) (many : 1 < N) : ∃ E, RealizingRound cert r E := by
  classical
  letI : Nonempty (CountAllocation.Population N ell) := ⟨⟨true, ⟨0, cert.leaders_positive⟩⟩⟩
  letI : Nonempty (VisibleNode (levels t H) r) :=
    ⟨⟨(levels_nonempty (H := H) r (by omega)).choose, (levels_nonempty (H := H) r (by omega)).choose_spec⟩⟩
  letI : Nonempty (VisibleNode (levels t H) (r + 1)) :=
    ⟨⟨(levels_nonempty (H := H) (r + 1) (by omega)).choose,
      (levels_nonempty (H := H) (r + 1) (by omega)).choose_spec⟩⟩
  obtain ⟨E, sc, deg, rec, exc⟩ := (cert.roundData r).physical_round_exists
    (cert.round_balanced r before) (cert.new_type_represented r before) (cert.type_connected r before many)
  refine ⟨E, sc, deg, ?_, exc⟩
  intro a v selected u
  have h := rec a v selected u
  unfold taggedIncoming
  convert h using 1
  · apply Finset.sum_congr rfl
    intro b _
    by_cases hb : cert.tag r b = some u <;> simp [Certificate.roundData, hb]
  · rfl

noncomputable def Certificate.historyTag (cert : Certificate ell N t H k) (r : Nat)
    (a : CountAllocation.Population N ell) : Option (FullHistory r) :=
  (cert.tag r a).map Subtype.val

theorem Certificate.historyTag_some (cert : Certificate ell N t H k) (r : Nat)
    (a : CountAllocation.Population N ell) (h : FullHistory r)
    (selected : cert.historyTag r a = some h) :
    ∃ u, cert.tag r a = some u ∧ u.val = h := by
  cases ht : cert.tag r a with
  | none => simp [Certificate.historyTag, ht] at selected
  | some u =>
    exact ⟨u, rfl, by simpa [Certificate.historyTag, ht] using selected⟩

theorem Certificate.historyTag_none_iff (cert : Certificate ell N t H k) (r : Nat)
    (a : CountAllocation.Population N ell) : cert.historyTag r a = none ↔ cert.tag r a = none := by
  cases ht : cert.tag r a <;> simp [Certificate.historyTag, ht]

noncomputable def Certificate.chosenRound (cert : Certificate ell N t H k)
    (rounds : ∀ r, r < t → ∃ E, RealizingRound cert r E) (r : Nat) :
    CountAllocation.Population N ell → CountAllocation.Population N ell → Nat :=
  if before : r < t then Classical.choose (rounds r before) else fun _ _ => 1

theorem Certificate.chosenRound_spec (cert : Certificate ell N t H k)
    (rounds : ∀ r, r < t → ∃ E, RealizingRound cert r E) (r : Nat) (before : r < t) :
    RealizingRound cert r (cert.chosenRound rounds r) := by
  unfold Certificate.chosenRound
  rw [dif_pos before]
  exact Classical.choose_spec (rounds r before)

noncomputable def Certificate.realizingNetwork (cert : Certificate ell N t H k)
    (rounds : ∀ r, r < t → ∃ E, RealizingRound cert r E) :
    Nat → CountAllocation.Population N ell → CountAllocation.Population N ell → Nat
  | 0 => fun _ _ => 1
  | r + 1 => cert.chosenRound rounds r

theorem Certificate.realizing_history (cert : Certificate ell N t H k)
    (rounds : ∀ r, r < t → ∃ E, RealizingRound cert r E) :
    ∀ r, r ≤ t → ∀ a h, cert.historyTag r a = some h →
      history (cert.realizingNetwork rounds) (CountAllocation.populationLeader N ell) r a = h := by
  classical
  apply selected_histories
  · intro a h selected
    obtain ⟨u, tagged, eq⟩ := cert.historyTag_some 0 a h selected
    exact (cert.group_label 0 u a ((cert.tag_some_iff 0 a u).mp tagged)).trans eq
  · intro r _ a v selected
    obtain ⟨u, tagged, rfl⟩ := cert.historyTag_some (r + 1) a v selected
    simp only [Certificate.historyTag, cert.tag_nested r a u tagged, Option.map_some]
    rfl
  · intro r before a v selected
    obtain ⟨u, tagged, rfl⟩ := cert.historyTag_some (r + 1) a v selected
    exact (cert.chosenRound_spec rounds r before).degrees a u tagged
  · intro r before a v selected h
    obtain ⟨v, tagged, rfl⟩ := cert.historyTag_some (r + 1) a v selected
    have spec := cert.chosenRound_spec rounds r before
    by_cases visible : h ∈ levels t H r
    · let u : VisibleNode (levels t H) r := ⟨h, visible⟩
      have same : taggedIncoming (cert.realizingNetwork rounds (r + 1)) (cert.historyTag r) h a =
          taggedIncoming (cert.chosenRound rounds r) (cert.tag r) u a := by
        unfold taggedIncoming
        apply Finset.sum_congr rfl
        intro b _
        cases hb : cert.tag r b with
        | none => simp [Certificate.historyTag, hb]
        | some w =>
          simp only [Certificate.historyTag, hb, Option.map_some, Option.some.injEq, Subtype.ext_iff]
          rfl
      exact same.trans (spec.receipts a v tagged u)
    · have absent : h ∉ v.val.2.2 := by
        intro member
        exact visible (VistaIsomorphism.message_mem_levels t H r v.val v.property h member)
      rw [Multiset.count_eq_zero.mpr absent]
      unfold taggedIncoming
      apply Finset.sum_eq_zero
      intro b _
      have ht : cert.historyTag r b ≠ some h := by
        intro hh
        obtain ⟨u, _, eq⟩ := cert.historyTag_some r b h hh
        exact visible (eq ▸ u.property)
      simp only [if_neg ht]
  · intro r before a v selected b outside
    obtain ⟨u, tagged, _⟩ := cert.historyTag_some (r + 1) a v selected
    exact (cert.chosenRound_spec rounds r before).exclude a u tagged b
      ((cert.historyTag_none_iff r b).mp outside)

/-- Per-round realizations assemble on the same allocated physical
population. The final selected set contains its designated observer, whose
history is exactly the requested intrinsic vista. -/
theorem Certificate.realization_of_rounds (cert : Certificate ell N t H k)
    (rounds : ∀ r, r < t → ∃ E, RealizingRound cert r E) :
    ∃ G : Nat → CountAllocation.Population N ell → CountAllocation.Population N ell → Nat,
      Admissible ell G (CountAllocation.populationLeader N ell) ∧
      ∃ a, history G (CountAllocation.populationLeader N ell) t a = H := by
  classical
  refine ⟨cert.realizingNetwork rounds, ?_, ?_⟩
  · refine ⟨cert.leaders_positive, CountAllocation.population_leaders N ell, ?_⟩
    intro r positive
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    by_cases before : r < t
    · exact (cert.chosenRound_spec rounds r before).connected
    · intro a b
      exact Relation.ReflTransGen.single (by simp [Certificate.realizingNetwork, Certificate.chosenRound, before])
  · let u : VisibleNode (levels t H) t := ⟨H, VistaIsomorphism.self_mem_levels t H⟩
    obtain ⟨a, ha⟩ := cert.group_nonempty t le_rfl u
    refine ⟨a, cert.realizing_history rounds t le_rfl a H ?_⟩
    simp only [Certificate.historyTag, (cert.tag_some_iff t a u).mpr ha, Option.map_some]
    rfl

theorem Certificate.realization_of_many (cert : Certificate ell N t H k) (many : 1 < N) :
    ∃ G : Nat → CountAllocation.Population N ell → CountAllocation.Population N ell → Nat,
      Admissible ell G (CountAllocation.populationLeader N ell) ∧
      ∃ a, history G (CountAllocation.populationLeader N ell) t a = H :=
  cert.realization_of_rounds (fun r before => cert.round_exists r before many)

end Counting.Realizability
