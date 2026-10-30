import Counting.X3CNormalize
import Mathlib.Data.Finset.Sort

namespace Counting.X3C

/-- An explicit indexed X3C input before duplicate triples are deleted. -/
structure RawInstance (q m : ℕ) where
  triples : Fin m → Finset (Fin (3 * q))
  triple_card : ∀ j, (triples j).card = 3

def RawInstance.IsExactCover {q m : ℕ} (I : RawInstance q m)
    (chosen : Finset (Fin m)) : Prop :=
  ∀ e : Fin (3 * q), (chosen.filter (fun j => e ∈ I.triples j)).card = 1

/-- Keep the first occurrence of each triple. -/
def RawInstance.kept {q m : ℕ} (I : RawInstance q m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∀ i, I.triples i = I.triples j → j ≤ i)

theorem RawInstance.kept_injective {q m : ℕ} (I : RawInstance q m) :
    Set.InjOn I.triples I.kept := by
  intro a ha b hb equal
  have amin := (Finset.mem_filter.mp ha).2
  have bmin := (Finset.mem_filter.mp hb).2
  exact le_antisymm (amin b equal.symm) (bmin a equal)

def RawInstance.representative {q m : ℕ} (I : RawInstance q m) (j : Fin m) : Fin m :=
  (Finset.univ.filter (fun i => I.triples i = I.triples j)).min'
    ⟨j, by simp⟩

theorem RawInstance.representative_triple {q m : ℕ} (I : RawInstance q m) (j : Fin m) :
    I.triples (I.representative j) = I.triples j := by
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun i => I.triples i = I.triples j)) ⟨j, by simp⟩)).2

theorem RawInstance.representative_kept {q m : ℕ} (I : RawInstance q m) (j : Fin m) :
    I.representative j ∈ I.kept := by
  simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi
  apply Finset.min'_le
  simp [hi, I.representative_triple j]

def RawInstance.deduplicate {q m : ℕ} (I : RawInstance q m) : Instance q I.kept.card where
  triples j := I.triples (I.kept.orderEmbOfFin rfl j)
  triple_card j := I.triple_card _
  distinct := by
    intro a b same
    apply (I.kept.orderEmbOfFin rfl).injective
    exact I.kept_injective (Finset.orderEmbOfFin_mem _ _ a)
      (Finset.orderEmbOfFin_mem _ _ b) same

def RawInstance.toDeduplicated {q m : ℕ} (I : RawInstance q m) (j : Fin m) :
    Fin I.kept.card :=
  (I.kept.orderIsoOfFin rfl).symm ⟨I.representative j, I.representative_kept j⟩

@[simp] theorem RawInstance.toDeduplicated_triple {q m : ℕ} (I : RawInstance q m) (j : Fin m) :
    I.deduplicate.triples (I.toDeduplicated j) = I.triples j := by
  change I.triples ((I.kept.orderIsoOfFin rfl) ((I.kept.orderIsoOfFin rfl).symm
    ⟨I.representative j, I.representative_kept j⟩)).val = I.triples j
  rw [OrderIso.apply_symm_apply]
  exact I.representative_triple j

theorem RawInstance.cover_injective {q m : ℕ} (I : RawInstance q m)
    (chosen : Finset (Fin m)) (cover : I.IsExactCover chosen) :
    Set.InjOn I.triples chosen := by
  intro a ha b hb same
  have nonempty : (I.triples a).Nonempty := Finset.card_pos.mp (by rw [I.triple_card]; omega)
  obtain ⟨e, he⟩ := nonempty
  obtain ⟨j, only⟩ := Finset.card_eq_one.mp (cover e)
  have amem : a ∈ chosen.filter (fun j => e ∈ I.triples j) := Finset.mem_filter.mpr ⟨ha, he⟩
  have bmem : b ∈ chosen.filter (fun j => e ∈ I.triples j) :=
    Finset.mem_filter.mpr ⟨hb, same ▸ he⟩
  rw [only, Finset.mem_singleton] at amem bmem
  exact amem.trans bmem.symm

theorem RawInstance.deduplicate_cover {q m : ℕ} (I : RawInstance q m)
    (chosen : Finset (Fin m)) (cover : I.IsExactCover chosen) :
    I.deduplicate.IsExactCover (chosen.image I.toDeduplicated) := by
  intro e
  rw [Finset.filter_image]
  simp only [I.toDeduplicated_triple]
  rw [Finset.card_image_of_injOn]
  · exact cover e
  · intro a ha b hb same
    apply I.cover_injective chosen cover (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    have := congrArg I.deduplicate.triples same
    simpa using this

theorem RawInstance.restore_cover {q m : ℕ} (I : RawInstance q m)
    (chosen : Finset (Fin I.kept.card)) (cover : I.deduplicate.IsExactCover chosen) :
    I.IsExactCover (chosen.image (I.kept.orderEmbOfFin rfl)) := by
  intro e
  rw [Finset.filter_image, Finset.card_image_of_injective _ (I.kept.orderEmbOfFin rfl).injective]
  exact cover e

theorem RawInstance.deduplicate_exactCover_iff {q m : ℕ} (I : RawInstance q m) :
    (∃ chosen, I.deduplicate.IsExactCover chosen) ↔ ∃ chosen, I.IsExactCover chosen :=
  ⟨fun ⟨chosen, cover⟩ => ⟨_, I.restore_cover chosen cover⟩,
    fun ⟨chosen, cover⟩ => ⟨_, I.deduplicate_cover chosen cover⟩⟩

theorem RawInstance.kept_card_le {q m : ℕ} (I : RawInstance q m) : I.kept.card ≤ m := by
  simpa only [kept, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun j => ∀ i, I.triples i = I.triples j → j ≤ i)
      Finset.univ)

/-- Delete duplicate triples and add two forced fresh triples. This
normalization is a concrete function on the explicit finite input. -/
def RawInstance.normalize {q m : ℕ} (I : RawInstance q m) :
    Instance (q + 1 + 1) (I.kept.card + 1 + 1) := I.deduplicate.pad.pad

theorem RawInstance.normalize_exactCover_iff {q m : ℕ} (I : RawInstance q m) :
    (∃ chosen, I.normalize.IsExactCover chosen) ↔ ∃ chosen, I.IsExactCover chosen :=
  I.deduplicate.pad_twice_exactCover_iff.trans I.deduplicate_exactCover_iff

theorem RawInstance.normalize_parameters {q m : ℕ} (I : RawInstance q m) :
    2 ≤ q + 1 + 1 ∧ I.kept.card + 1 + 1 ≤ m + 2 := by
  have := I.kept_card_le
  omega

end Counting.X3C
