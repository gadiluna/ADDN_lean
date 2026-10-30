import Counting.SmallPrefixRound

namespace Counting.SmallPrefix
open DirectedCounting
variable {A : Type} [Fintype A] [DecidableEq A]

def hiddenDegree (N M : Nat) := N * M + M + 1
def degreeBound (N M : Nat) := 2 * N * M + N + M + 2

noncomputable def step (E : A → A → Nat) (S : Finset A) (M : Nat) : A → A → Nat :=
  if h : ∃ q, q ∉ S then normalize E S h.choose (hiddenDegree (Fintype.card A) M) else E

theorem kept_le (E : A → A → Nat) (S : Finset A) (M : Nat)
    (labels : ∀ a b, b ∈ S → E a b ≤ M) (a : A) : kept E S a ≤ Fintype.card A * M := by
  unfold kept
  calc
    _ ≤ ∑ _b : A, M := Finset.sum_le_sum (by
      intro b _; split_ifs with hb; exact labels a b hb; exact Nat.zero_le _)
    _ = _ := by simp

theorem step_visible (E : A → A → Nat) (S : Finset A) (M : Nat)
    (a b : A) (visible : b ∈ S) : step E S M a b = E a b := by
  classical
  unfold step
  split_ifs with h
  · exact normalize_visible _ _ _ _ _ _ visible
  · rfl

theorem step_visible_degree (E : A → A → Nat) (S : Finset A) (M : Nat)
    (a : A) (visible : a ∈ S) : (∑ b, step E S M a b) = ∑ b, E a b := by
  classical
  unfold step
  split_ifs with h
  · exact normalize_visible_degree _ _ _ _ h.choose_spec _ visible
  · rfl

theorem step_connected (E : A → A → Nat) (S : Finset A) (M : Nat)
    (labels : ∀ a b, b ∈ S → E a b ≤ M)
    (connected : StronglyConnected (fun a b => 0 < E a b)) :
    StronglyConnected (fun a b => 0 < step E S M a b) := by
  classical
  unfold step
  split_ifs with h
  · apply normalize_connected _ _ _ _ h.choose_spec _ connected
    intro a
    have := kept_le E S M labels a
    unfold hiddenDegree
    omega
  · exact connected

theorem step_degree_bound (E : A → A → Nat) (S : Finset A) (M : Nat)
    (labels : ∀ a b, b ∈ S → E a b ≤ M)
    (degrees : ∀ a ∈ S, (∑ b, E a b) ≤ M) (a : A) :
    (∑ b, step E S M a b) ≤ degreeBound (Fintype.card A) M := by
  classical
  by_cases visible : a ∈ S
  · rw [step_visible_degree _ _ _ _ visible]
    exact (degrees a visible).trans (by unfold degreeBound; omega)
  · have existsHidden : ∃ q, q ∉ S := ⟨a, visible⟩
    rw [step, dif_pos existsHidden]
    by_cases eq : a = existsHidden.choose
    · subst a
      have bound := normalize_hub_degree_le E S existsHidden.choose
        (hiddenDegree (Fintype.card A) M) existsHidden.choose_spec
      have keptBound := kept_le E S M labels existsHidden.choose
      unfold hiddenDegree degreeBound at *
      nlinarith
    · rw [normalize_hidden_degree _ _ _ _ existsHidden.choose_spec _ visible eq
        ((kept_le E S M labels a).trans (by unfold hiddenDegree; omega))]
      unfold hiddenDegree degreeBound
      nlinarith

noncomputable def nextHistory (r : Nat) (E : A → A → Nat) (state : A → FullHistory r)
    (a : A) : FullHistory (r + 1) := (state a, ∑ b, E a b, incoming E state a)

/-- Each ordinary hidden child is determined by its old history. There is
at most one additional singleton history, that of the chosen hidden hub. -/
theorem step_card (r : Nat) (E : A → A → Nat) (S : Finset A) (M : Nat)
    (labels : ∀ a b, b ∈ S → E a b ≤ M)
    (state : A → FullHistory r) (visibleHistory : A → FullHistory (r + 1))
    (preserved : ∀ a ∈ S, nextHistory r (step E S M) state a = visibleHistory a) :
    (Finset.univ.image (nextHistory r (step E S M) state)).card ≤
      (S.image visibleHistory).card + (Finset.univ.image state).card + 1 := by
  classical
  by_cases hidden : ∃ q, q ∉ S
  · let q := hidden.choose
    let D := hiddenDegree (Fintype.card A) M
    let lift : FullHistory r → FullHistory (r + 1) := fun h => (h, D, {state q})
    have ordinary (a : A) (outside : a ∉ S) (different : a ≠ q) :
        nextHistory r (step E S M) state a = lift (state a) := by
      dsimp [nextHistory, step]
      rw [dif_pos hidden]
      rw [normalize_hidden_degree _ _ _ _ hidden.choose_spec _ outside different
        ((kept_le E S M labels a).trans (by unfold hiddenDegree; omega)),
        normalize_hidden_incoming _ _ _ _ _ _ outside different]
    have subset : Finset.univ.image (nextHistory r (step E S M) state) ⊆
        S.image visibleHistory ∪ (Finset.univ.image state).image lift ∪
          {nextHistory r (step E S M) state q} := by
      intro h hh
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hh
      by_cases visible : a ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨a, visible, (preserved a visible).symm⟩))
      · by_cases eq : a = q
        · subst a; simp
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨state a,
            Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩, (ordinary a visible eq).symm⟩
    have h := (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
    have h₂ := Finset.card_union_le (S.image visibleHistory) ((Finset.univ.image state).image lift)
    have h₃ := Finset.card_image_le (s := Finset.univ.image state) (f := lift)
    simp only [Finset.card_singleton] at h
    omega
  · have all : S = Finset.univ := Finset.eq_univ_of_forall (by simpa using hidden)
    have eq : nextHistory r (step E S M) state = visibleHistory :=
      funext (fun a => preserved a (by simp [all]))
    rw [eq, all]
    omega

end Counting.SmallPrefix
