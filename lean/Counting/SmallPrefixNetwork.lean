import Counting.SmallPrefixStep
import Counting.RealizabilitySupport

namespace Counting.SmallPrefix
open DirectedCounting TimingProtocolLocal
variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def visibleAgents (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) : Finset A :=
  Finset.univ.filter (fun a => history G leader r a ∈ levels t H r)

omit [DecidableEq A] in
@[simp] theorem mem_visibleAgents {G : Nat → A → A → Nat} {leader : A → Bool}
    {t : Nat} {H : FullHistory t} {r : Nat} {a : A} :
    a ∈ visibleAgents G leader t H r ↔ history G leader r a ∈ levels t H r := by
  simp [visibleAgents]

omit [DecidableEq A] in
theorem edge_le_receipt (G : Nat → A → A → Nat) (leader : A → Bool)
    (r : Nat) (a b : A) : G (r + 1) a b ≤
      red r (history G leader r a) (history G leader (r + 1) b) := by
  classical
  unfold red
  change G (r + 1) a b ≤ (incoming (G (r + 1)) (history G leader r) b).count _
  rw [count_incoming]
  simpa using Finset.single_le_sum
    (f := fun y => if history G leader r y = history G leader r a then G (r + 1) y b else 0)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)

omit [DecidableEq A] in
theorem visible_source (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (a b : A)
    (target : b ∈ visibleAgents G leader t H (r + 1)) (edge : 0 < G (r + 1) a b) :
    a ∈ visibleAgents G leader t H r := by
  apply mem_visibleAgents.mpr
  apply VistaIsomorphism.message_mem_levels t H r _ (mem_visibleAgents.mp target)
  exact Multiset.count_pos.mp (edge.trans_le (edge_le_receipt G leader r a b))

omit [DecidableEq A] in
theorem visible_edge_bound (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t)
    (a b : A) (target : b ∈ visibleAgents G leader t H (r + 1)) :
    G (r + 1) a b ≤ Realizability.maxLabel 0 t H := by
  by_cases positive : 0 < G (r + 1) a b
  · exact (edge_le_receipt G leader r a b).trans
      (Realizability.red_le_maxLabel 0 t H r before _
        (mem_visibleAgents.mp (visible_source G leader t H r a b target positive)) _
        (mem_visibleAgents.mp target))
  · omega

omit [DecidableEq A] in
theorem visible_degree_bound (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t)
    (a : A) (visible : a ∈ visibleAgents G leader t H (r + 1)) :
    (∑ b, G (r + 1) a b) ≤ Realizability.maxLabel 0 t H :=
  Realizability.degree_le_maxLabel 0 t H r before _ (mem_visibleAgents.mp visible)

noncomputable def network (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) : Nat → A → A → Nat
  | 0 => G 0
  | r + 1 => if r < t then
      step (G (r + 1)) (visibleAgents G leader t H (r + 1)) (Realizability.maxLabel 0 t H)
    else fun _ _ => 1

theorem network_admissible (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) {ell : Nat} (valid : Admissible ell G leader) :
    Admissible ell (network G leader t H) leader := by
  refine ⟨valid.positive, valid.leaders, ?_⟩
  intro r positive
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  by_cases before : r < t
  · simp only [network, if_pos before]
    exact step_connected _ _ _ (visible_edge_bound G leader t H r before)
      (valid.connected (r + 1) (by omega))
  · intro a b
    exact .single (by simp [network, before])

/-- Original visible histories are unchanged on their entire fibers. -/
theorem network_history_visible (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) :
    ∀ r, r ≤ t → ∀ a, a ∈ visibleAgents G leader t H r →
      history (network G leader t H) leader r a = history G leader r a := by
  classical
  intro r
  induction r with
  | zero => intro _ _ _; rfl
  | succ r ih =>
    intro within a visible
    have before : r < t := by omega
    have parent : a ∈ visibleAgents G leader t H r :=
      mem_visibleAgents.mpr (VistaIsomorphism.parent_mem_levels t H r _
        (mem_visibleAgents.mp visible))
    apply Prod.ext (ih (by omega) a parent)
    apply Prod.ext
    · change (∑ b, network G leader t H (r + 1) a b) = ∑ b, G (r + 1) a b
      simp only [network, if_pos before]
      exact step_visible_degree _ _ _ a visible
    · change incoming (network G leader t H (r + 1))
        (history (network G leader t H) leader r) a = incoming (G (r + 1)) (history G leader r) a
      unfold incoming
      apply Finset.sum_congr rfl
      intro b _
      have edges : network G leader t H (r + 1) b a = G (r + 1) b a := by
        simp only [network, if_pos before]
        exact step_visible _ _ _ b a visible
      rw [edges]
      by_cases edge : 0 < G (r + 1) b a
      · rw [ih (by omega) b (visible_source G leader t H r b a visible edge)]
      · have zero : G (r + 1) b a = 0 := by omega
        simp [zero]

theorem network_observer (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (observer : A) :
    history (network G leader t (history G leader t observer)) leader t observer =
      history G leader t observer :=
  network_history_visible G leader t _ t le_rfl observer
    (mem_visibleAgents.mpr (VistaIsomorphism.self_mem_levels _ _))

noncomputable def fullLevel (G : Nat → A → A → Nat) (leader : A → Bool) (r : Nat) :
    Finset (FullHistory r) := Finset.univ.image (history G leader r)

theorem network_level_step (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t) :
    (fullLevel (network G leader t H) leader (r + 1)).card ≤
      (levels t H (r + 1)).card + (fullLevel (network G leader t H) leader r).card + 1 := by
  classical
  have h := step_card r (G (r + 1)) (visibleAgents G leader t H (r + 1))
    (Realizability.maxLabel 0 t H) (visible_edge_bound G leader t H r before)
    (history (network G leader t H) leader r) (history G leader (r + 1))
    (by intro a ha; simpa only [history, network, if_pos before, nextHistory] using
      network_history_visible G leader t H (r + 1) (by omega) a ha)
  have sub : (visibleAgents G leader t H (r + 1)).image (history G leader (r + 1)) ⊆
      levels t H (r + 1) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact mem_visibleAgents.mp ha
  have bound := Finset.card_le_card sub
  have eq : fullLevel (network G leader t H) leader (r + 1) =
      Finset.univ.image (nextHistory r
        (step (G (r + 1)) (visibleAgents G leader t H (r + 1)) (Realizability.maxLabel 0 t H))
        (history (network G leader t H) leader r)) := by
    simp only [fullLevel, history, network, if_pos before]
    rfl
  rw [eq]
  exact h.trans (by unfold fullLevel; omega)

/-- Exact level bound in the manuscript's normal-form lemma. -/
theorem network_level_bound (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (within : r ≤ t) :
    (fullLevel (network G leader t H) leader r).card ≤
      (∑ j ∈ Finset.range (r + 1), (levels t H j).card) + r + 2 := by
  induction r with
  | zero =>
    have bound : (fullLevel (network G leader t H) leader 0).card ≤ 2 := by
      letI : Fintype (FullHistory 0) := inferInstanceAs (Fintype Bool)
      exact (Finset.card_le_univ _).trans_eq Fintype.card_bool
    omega
  | succ r ih =>
    have old := ih (by omega)
    have next := network_level_step G leader t H r (by omega)
    rw [Finset.sum_range_succ]
    omega

theorem network_degree_bound (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t) (a : A) :
    (∑ b, network G leader t H (r + 1) a b) ≤
      degreeBound (Fintype.card A) (Realizability.maxLabel 0 t H) := by
  simp only [network, if_pos before]
  exact step_degree_bound _ _ _ (visible_edge_bound G leader t H r before)
    (visible_degree_bound G leader t H r before) a

end Counting.SmallPrefix
