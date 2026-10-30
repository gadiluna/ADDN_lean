import Counting.SmallPrefixNetwork
import Counting.EncodingRecognitionBounds

namespace Counting.SmallPrefix
open DirectedCounting TimingProtocolLocal

def labelCap (N M : Nat) := 4 * (N + 1) ^ 2 * (M + 1)

theorem degreeBound_le (N M : Nat) : degreeBound N M ≤ 4 * (N + 1) * (M + 1) := by
  unfold degreeBound
  nlinarith

theorem labelCap_bounds (N M : Nat) :
    N ≤ labelCap N M ∧ degreeBound N M ≤ labelCap N M ∧ N * degreeBound N M ≤ labelCap N M := by
  have h := degreeBound_le N M
  have hN := Nat.mul_le_mul_left N h
  unfold labelCap
  constructor
  · nlinarith [Nat.zero_le (N ^ 2 * M), Nat.zero_le (N ^ 2), Nat.zero_le (N * M)]
  constructor
  · nlinarith [Nat.zero_le (N ^ 2 * M), Nat.zero_le (N ^ 2), Nat.zero_le (N * M)]
  · nlinarith [Nat.zero_le (N * M)]

/-- Linear binary length in the original label length and log population. -/
theorem labelCap_size (N M : Nat) : (labelCap N M).size ≤ 2 * N.size + M.size + 6 := by
  have n : N + 1 ≤ 2 ^ (N.size + 1) := by
    have := Nat.lt_size_self N
    rw [pow_succ]
    omega
  have m : M + 1 ≤ 2 ^ (M.size + 1) := by
    have := Nat.lt_size_self M
    rw [pow_succ]
    omega
  have bound : labelCap N M ≤ 2 ^ (2 * N.size + M.size + 5) := by
    unfold labelCap
    calc
      _ ≤ 4 * (2 ^ (N.size + 1)) ^ 2 * 2 ^ (M.size + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left n 2)) m
      _ = _ := by
        rw [← pow_mul]
        change 2 ^ 2 * 2 ^ ((N.size + 1) * 2) * 2 ^ (M.size + 1) = _
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have h := Nat.size_le_size bound
  simpa [Nat.size_pow, Nat.add_assoc] using h

variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def anonymity (G : Nat → A → A → Nat) (leader : A → Bool)
    (r : Nat) (h : FullHistory r) : Nat :=
  (Finset.univ.filter (fun a => history G leader r a = h)).card

omit [DecidableEq A] in
theorem anonymity_le (G : Nat → A → A → Nat) (leader : A → Bool)
    (r : Nat) (h : FullHistory r) : anonymity G leader r h ≤ Fintype.card A :=
  Finset.card_le_univ _

theorem network_degree_label (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t)
    (v : FullHistory (r + 1)) (member : v ∈ fullLevel (network G leader t H) leader (r + 1)) :
    degree r v ≤ degreeBound (Fintype.card A) (Realizability.maxLabel 0 t H) := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp member
  exact network_degree_bound G leader t H r before a

theorem network_red_label (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (before : r < t)
    (u : FullHistory r) (v : FullHistory (r + 1))
    (member : v ∈ fullLevel (network G leader t H) leader (r + 1)) :
    red r u v ≤ Fintype.card A * degreeBound (Fintype.card A) (Realizability.maxLabel 0 t H) := by
  classical
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp member
  unfold red
  change (incoming _ _ b).count u ≤ _
  rw [count_incoming]
  calc
    _ ≤ ∑ _a : A, degreeBound (Fintype.card A) (Realizability.maxLabel 0 t H) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans
          (network_degree_bound G leader t H r before a)
      · exact Nat.zero_le _
    _ = _ := by simp

/-- Bounds every numeric history-tree label, including hidden classes. -/
theorem network_labels (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) :
    (∀ r (v : FullHistory r), anonymity (network G leader t H) leader r v ≤
      labelCap (Fintype.card A) (Realizability.maxLabel 0 t H)) ∧
    (∀ r, r < t → ∀ v ∈ fullLevel (network G leader t H) leader (r + 1),
      degree r v ≤ labelCap (Fintype.card A) (Realizability.maxLabel 0 t H)) ∧
    (∀ r, r < t → ∀ u (v : FullHistory (r + 1)),
      v ∈ fullLevel (network G leader t H) leader (r + 1) →
      red r u v ≤ labelCap (Fintype.card A) (Realizability.maxLabel 0 t H)) := by
  have bounds := labelCap_bounds (Fintype.card A) (Realizability.maxLabel 0 t H)
  refine ⟨fun r v => (anonymity_le _ _ r v).trans bounds.1, ?_, ?_⟩
  · intro r hr v hv
    exact (network_degree_label G leader t H r hr v hv).trans bounds.2.1
  · intro r hr u v hv
    exact (network_red_label G leader t H r hr u v hv).trans bounds.2.2

theorem depth_le_nodeCount (t : Nat) (H : FullHistory t) : t + 1 ≤ Realizability.nodeCount t H := by
  unfold Realizability.nodeCount
  calc
    t + 1 = ∑ _j ∈ Finset.range (t + 1), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j hj =>
      Finset.card_pos.mpr (Realizability.levels_nonempty j (by have := Finset.mem_range.mp hj; omega)))

theorem network_level_uniform (G : Nat → A → A → Nat) (leader : A → Bool)
    (t : Nat) (H : FullHistory t) (r : Nat) (within : r ≤ t) :
    (fullLevel (network G leader t H) leader r).card ≤ 2 * Realizability.nodeCount t H + 1 := by
  have h := network_level_bound G leader t H r within
  have sumBound : (∑ j ∈ Finset.range (r + 1), (levels t H j).card) ≤ Realizability.nodeCount t H :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; omega)
  have depth := depth_le_nodeCount t H
  omega

end Counting.SmallPrefix
