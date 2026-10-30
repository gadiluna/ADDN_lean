import Counting.RealizabilityBalance

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ) (observer : V)

abbrev ActualVertex (r : ℕ) := RoundVertex (Fintype.card V)
  (levels t (history G leader t observer)) (selectedCounts G leader t observer) r

abbrev actualArc (r : ℕ) := roundArc (Fintype.card V)
  (levels t (history G leader t observer)) (selectedCounts G leader t observer) r

theorem hidden_positive_of_outside (r : ℕ) (before : r < t) (a : V)
    (outside : a ∉ supportAt G t observer (r + 1)) :
    0 < hidden (Fintype.card V) (levels t (history G leader t observer))
      (selectedCounts G leader t observer) r := by
  apply Nat.pos_of_ne_zero
  intro zero
  have := (selected_hidden_zero_iff G leader t observer r before).mp zero
  exact outside (by rw [this]; exact Finset.mem_univ _)

noncomputable def projectAgent (r : ℕ) (before : r < t) (a : V) : ActualVertex G leader t observer r := by
  classical
  exact if ha : a ∈ supportAt G t observer (r + 1) then
    .inl ⟨history G leader (r + 1) a, selected_history_visible G leader t observer (r + 1) (by omega) a ha⟩
  else .inr (.inr ⟨0, by
    unfold outsideSize
    rw [if_pos (hidden_positive_of_outside G leader t observer r before a ha)]
    omega⟩)

theorem project_selected (r : ℕ) (before : r < t) (a : V)
    (ha : a ∈ supportAt G t observer (r + 1)) :
    projectAgent G leader t observer r before a =
      .inl ⟨history G leader (r + 1) a, selected_history_visible G leader t observer (r + 1) (by omega) a ha⟩ := by
  simp only [projectAgent, dif_pos ha]

theorem project_outside (r : ℕ) (before : r < t) (a : V)
    (ha : a ∉ supportAt G t observer (r + 1))
    (j : Fin (outsideSize (Fintype.card V) (levels t (history G leader t observer))
      (selectedCounts G leader t observer) r)) :
    projectAgent G leader t observer r before a = .inr (.inr j) := by
  simp only [projectAgent, dif_neg ha]
  congr 2
  apply Fin.ext
  change 0 = j.val
  have hj := j.isLt
  simp only [outsideSize, if_pos (hidden_positive_of_outside G leader t observer r before a ha)] at hj
  omega

theorem leaving_positive_of_departure (r : ℕ) (before : r < t) (H : FullHistory r)
    (a : V) (old : a ∈ selectedGroup G leader t observer r H)
    (outside : a ∉ supportAt G t observer (r + 1)) :
    0 < leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H := by
  classical
  rw [leaving_eq_difference_card G leader t observer r before H]
  exact Finset.card_pos.mpr ⟨a, Finset.mem_sdiff.mpr ⟨old,
    fun h => outside (Finset.mem_filter.mp h).1⟩⟩

theorem degree_positive_of_edge (r : ℕ) (a b : V) (edge : 0 < G (r + 1) a b) :
    0 < degree r (history G leader (r + 1) a) := by
  exact lt_of_lt_of_le edge (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))

theorem red_positive_of_edge (r : ℕ) (before : r < t) (a b : V)
    (selected : b ∈ supportAt G t observer (r + 1)) (edge : 0 < G (r + 1) a b) :
    0 < red r (history G leader r a) (history G leader (r + 1) b) := by
  classical
  have old : a ∈ supportAt G t observer r := by
    by_contra h
    have := no_incoming_from_unselected G t observer r before a b h selected
    omega
  rw [selected_red G leader t observer r before _ b selected]
  have member : a ∈ selectedGroup G leader t observer r (history G leader r a) :=
    Finset.mem_filter.mpr ⟨old, rfl⟩
  exact lt_of_lt_of_le edge (Finset.single_le_sum (f := fun x => G (r + 1) x b)
    (fun _ _ => Nat.zero_le _) member)

theorem project_edge (r : ℕ) (before : r < t) (a b : V) (edge : 0 < G (r + 1) a b) :
    Relation.ReflTransGen (actualArc G leader t observer r)
      (projectAgent G leader t observer r before a) (projectAgent G leader t observer r before b) := by
  classical
  by_cases ha : a ∈ supportAt G t observer (r + 1)
  · have au := selected_history_visible G leader t observer r (by omega) a
      (supportAt_nested G t observer r before ha)
    let u : VisibleNode (levels t (history G leader t observer)) r := ⟨history G leader r a, au⟩
    have first : actualArc G leader t observer r (projectAgent G leader t observer r before a) (.inr (.inl u)) := by
      rw [project_selected G leader t observer r before a ha]
      exact ⟨rfl, degree_positive_of_edge G leader r a b edge⟩
    apply (Relation.ReflTransGen.single first).trans
    apply Relation.ReflTransGen.single
    by_cases hb : b ∈ supportAt G t observer (r + 1)
    · rw [project_selected G leader t observer r before b hb]
      exact red_positive_of_edge G leader t observer r before a b hb edge
    · simp only [projectAgent, dif_neg hb]
      change 0 < leaving _ _ _ _ ∨ demand _ _ _ _ < supply _ _ _ _
      by_cases depart : 0 < leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r u.val
      · exact Or.inl depart
      · exact Or.inr (selected_supply_gt_demand G leader t observer r before u.val (by omega) a b
          (Finset.mem_filter.mpr ⟨ha, rfl⟩) hb edge)
  · by_cases hb : b ∈ supportAt G t observer (r + 1)
    · have old : a ∈ supportAt G t observer r := by
        by_contra h
        have := no_incoming_from_unselected G t observer r before a b h hb
        omega
      let u : VisibleNode (levels t (history G leader t observer)) r :=
        ⟨history G leader r a, selected_history_visible G leader t observer r (by omega) a old⟩
      have first : actualArc G leader t observer r (projectAgent G leader t observer r before a) (.inr (.inl u)) := by
        simp only [projectAgent, dif_neg ha]
        exact leaving_positive_of_departure G leader t observer r before u.val a
          (Finset.mem_filter.mpr ⟨old, rfl⟩) ha
      apply (Relation.ReflTransGen.single first).trans
      apply Relation.ReflTransGen.single
      rw [project_selected G leader t observer r before b hb]
      exact red_positive_of_edge G leader t observer r before a b hb edge
    · have same : projectAgent G leader t observer r before a = projectAgent G leader t observer r before b := by
        simp only [projectAgent, dif_neg ha, dif_neg hb]
      rw [same]

theorem project_reachable (r : ℕ) (before : r < t) (a b : V)
    (path : Relation.ReflTransGen (fun a b => 0 < G (r + 1) a b) a b) :
    Relation.ReflTransGen (actualArc G leader t observer r)
      (projectAgent G leader t observer r before a) (projectAgent G leader t observer r before b) := by
  induction path with
  | refl => exact .refl
  | @tail b c p edge ih => exact ih.trans (project_edge G leader t observer r before b c edge)

theorem exists_positive_outgoing (r : ℕ)
    (connected : StronglyConnected (fun a b => 0 < G (r + 1) a b))
    (many : 1 < Fintype.card V) (a : V) : ∃ b, 0 < G (r + 1) a b := by
  classical
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card many a
  obtain ⟨x, y, hx, _, edge⟩ := exists_edge_leaving connected
    (Q := {a}) ⟨a, rfl⟩ ⟨b, hb⟩
  exact ⟨y, hx ▸ edge⟩

theorem auxiliary_access (r : ℕ) (before : r < t)
    (connected : StronglyConnected (fun a b => 0 < G (r + 1) a b))
    (many : 1 < Fintype.card V) (u : VisibleNode (levels t (history G leader t observer)) r) :
    ∃ a b, actualArc G leader t observer r (projectAgent G leader t observer r before a) (.inr (.inl u)) ∧
      actualArc G leader t observer r (.inr (.inl u)) (projectAgent G leader t observer r before b) := by
  classical
  have positive := (selectedCounts_positive_iff G leader t observer r (by omega) u.val).mpr u.property
  obtain ⟨a, ha⟩ := Finset.card_pos.mp positive
  obtain ⟨old, historyEq⟩ := Finset.mem_filter.mp ha
  by_cases selected : a ∈ supportAt G t observer (r + 1)
  · obtain ⟨b, edge⟩ := exists_positive_outgoing G r connected many a
    refine ⟨a, b, ?_, ?_⟩
    · rw [project_selected G leader t observer r before a selected]
      exact ⟨historyEq, degree_positive_of_edge G leader r a b edge⟩
    · by_cases hb : b ∈ supportAt G t observer (r + 1)
      · rw [project_selected G leader t observer r before b hb]
        change 0 < red r u.val (history G leader (r + 1) b)
        rw [← historyEq]
        exact red_positive_of_edge G leader t observer r before a b hb edge
      · simp only [projectAgent, dif_neg hb]
        change 0 < leaving _ _ _ _ ∨ demand _ _ _ _ < supply _ _ _ _
        by_cases depart : 0 < leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r u.val
        · exact Or.inl depart
        · exact Or.inr (selected_supply_gt_demand G leader t observer r before u.val (by omega) a b
            (Finset.mem_filter.mpr ⟨selected, historyEq⟩) hb edge)
  · have depart := leaving_positive_of_departure G leader t observer r before u.val a ha selected
    refine ⟨a, a, ?_, ?_⟩
    · simp only [projectAgent, dif_neg selected]
      exact depart
    · simp only [projectAgent, dif_neg selected]
      exact Or.inl depart

theorem vertex_access (r : ℕ) (before : r < t)
    (connected : StronglyConnected (fun a b => 0 < G (r + 1) a b))
    (many : 1 < Fintype.card V) (x : ActualVertex G leader t observer r) :
    ∃ a b, Relation.ReflTransGen (actualArc G leader t observer r) x (projectAgent G leader t observer r before a) ∧
      Relation.ReflTransGen (actualArc G leader t observer r) (projectAgent G leader t observer r before b) x := by
  classical
  rcases x with v | u | j
  · have positive := (selectedCounts_positive_iff G leader t observer (r + 1) (by omega) v.val).mpr v.property
    obtain ⟨a, ha⟩ := Finset.card_pos.mp positive
    obtain ⟨selected, same⟩ := Finset.mem_filter.mp ha
    have heq : projectAgent G leader t observer r before a = .inl v := by
      rw [project_selected G leader t observer r before a selected]
      congr 1
      exact Subtype.ext same
    exact ⟨a, a, heq ▸ .refl, heq ▸ .refl⟩
  · obtain ⟨a, b, enter, leave⟩ := auxiliary_access G leader t observer r before connected many u
    exact ⟨b, a, .single leave, .single enter⟩
  · have positive : 0 < hidden (Fintype.card V) (levels t (history G leader t observer))
        (selectedCounts G leader t observer) r := by
      have hj := j.isLt
      by_contra hn
      simp [outsideSize, hn] at hj
    have outside : ∃ a, a ∉ supportAt G t observer (r + 1) := by
      by_contra hn
      push Not at hn
      have zero := (selected_hidden_zero_iff G leader t observer r before).mpr (Finset.eq_univ_of_forall hn)
      omega
    obtain ⟨a, ha⟩ := outside
    have heq := project_outside G leader t observer r before a ha j
    exact ⟨a, a, heq ▸ .refl, heq ▸ .refl⟩

/-- Projecting physical paths proves precisely the auxiliary graph test
required by the fixed-order certificate, including each auxiliary vertex. -/
theorem selected_connected (r : ℕ) (before : r < t)
    (connected : StronglyConnected (fun a b => 0 < G (r + 1) a b))
    (many : 1 < Fintype.card V) : StronglyConnected (actualArc G leader t observer r) := by
  intro x y
  obtain ⟨a, _, first, _⟩ := vertex_access G leader t observer r before connected many x
  obtain ⟨_, b, _, last⟩ := vertex_access G leader t observer r before connected many y
  exact first.trans ((project_reachable G leader t observer r before a b (connected a b)).trans last)

end Counting.Realizability
