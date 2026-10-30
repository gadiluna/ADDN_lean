import Counting.RealizabilityPumping
import Counting.SupportBound

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal PaperHistory

/-- Number of visible nonroot nodes in the intrinsic vista syntax. -/
noncomputable def nodeCount (t : ℕ) (H : FullHistory t) : ℕ :=
  ∑ r ∈ Finset.range (t + 1), (levels t H r).card

noncomputable def maxRed (t : ℕ) (H : FullHistory t) : ℕ :=
  (Finset.range t).sup (fun r => (levels t H r).sup (fun u =>
    (levels t H (r + 1)).sup (fun v => red r u v)))

noncomputable def maxDegree (t : ℕ) (H : FullHistory t) : ℕ :=
  (Finset.range t).sup (fun r => (levels t H (r + 1)).sup (fun v => degree r v))

/-- The same maximum M as in the paper, including the known leader count
and both kinds of numerical labels. -/
noncomputable def maxLabel (ell t : ℕ) (H : FullHistory t) : ℕ :=
  max ell (max (maxRed t H) (maxDegree t H))

noncomputable def supportBound (ell t : ℕ) (H : FullHistory t) : ℕ :=
  (1 + nodeCount t H * maxLabel ell t H) ^ t

theorem red_le_maxLabel (ell t : ℕ) (H : FullHistory t) (r : ℕ) (before : r < t)
    (u : FullHistory r) (hu : u ∈ levels t H r)
    (v : FullHistory (r + 1)) (hv : v ∈ levels t H (r + 1)) :
    red r u v ≤ maxLabel ell t H := by
  have redBound : red r u v ≤ maxRed t H :=
    (Finset.le_sup (f := red r u) hv).trans
      ((Finset.le_sup (f := fun u => (levels t H (r + 1)).sup (red r u)) hu).trans
        (Finset.le_sup (f := fun r => (levels t H r).sup (fun u =>
          (levels t H (r + 1)).sup (red r u))) (Finset.mem_range.mpr before)))
  exact redBound.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))

theorem degree_le_maxLabel (ell t : ℕ) (H : FullHistory t) (r : ℕ) (before : r < t)
    (v : FullHistory (r + 1)) (hv : v ∈ levels t H (r + 1)) :
    degree r v ≤ maxLabel ell t H := by
  have degreeBound : degree r v ≤ maxDegree t H :=
    (Finset.le_sup (f := degree r) hv).trans
      (Finset.le_sup (f := fun r => (levels t H (r + 1)).sup (degree r)) (Finset.mem_range.mpr before))
  exact degreeBound.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ) (observer : V)

theorem nodeCount_actual : nodeCount t (history G leader t observer) =
    SupportBound.vistaNodeCount G leader t observer := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [levels_eq_image G leader t r (by have := Finset.mem_range.mp hr; omega) observer]
  exact Finset.card_image_of_injective _ (nodeHistory_injective G leader r)

theorem actual_red_le_maxLabel (ell r : ℕ) (before : r < t)
    (u : Node G leader r) (hu : u ∈ visibleNodes G leader r (t - r) observer)
    (v : Node G leader (r + 1)) (hv : v ∈ visibleNodes G leader (r + 1) (t - (r + 1)) observer) :
    redMultiplicity G leader r u v ≤ maxLabel ell t (history G leader t observer) := by
  have old : nodeHistory G leader r u ∈ levels t (history G leader t observer) r := by
    rw [levels_eq_image G leader t r (by omega) observer]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have new : nodeHistory G leader (r + 1) v ∈ levels t (history G leader t observer) (r + 1) := by
    rw [levels_eq_image G leader t (r + 1) (by omega) observer]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  simpa only [nodeHistory_red] using red_le_maxLabel ell t (history G leader t observer) r before _ old _ new

/-- The support bound is determined entirely by the observer's intrinsic
vista. It therefore applies uniformly across all its realizations. -/
theorem initial_support_le_bound (ell : ℕ) :
    (causalSupport G 0 t observer).card ≤ supportBound ell t (history G leader t observer) := by
  have bound := SupportBound.initial_support_bound_of_vista_labels G leader t observer
    (maxLabel ell t (history G leader t observer)) (actual_red_le_maxLabel G leader t observer ell)
  simpa only [supportBound, nodeCount_actual] using bound

theorem selected_initial_le_bound (ell : ℕ) :
    (∑ u ∈ levels t (history G leader t observer) 0, selectedCounts G leader t observer 0 u) ≤
      supportBound ell t (history G leader t observer) := by
  rw [selectedCounts_total G leader t observer 0 (Nat.zero_le t)]
  exact initial_support_le_bound G leader t observer ell

end Counting.Realizability
