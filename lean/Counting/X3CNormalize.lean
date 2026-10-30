import Counting.X3CEquation

namespace Counting.X3C

def oldElement (q : ℕ) : Fin (3 * q) ↪ Fin (3 * (q + 1)) where
  toFun e := ⟨e.val, by have := e.isLt; omega⟩
  inj' := by
    intro a b equal
    exact Fin.ext (congrArg (fun x : Fin (3 * (q + 1)) => x.val) equal)

def freshElement (q : ℕ) : Fin 3 ↪ Fin (3 * (q + 1)) where
  toFun e := ⟨3 * q + e.val, by have := e.isLt; omega⟩
  inj' := by
    intro a b equal
    apply Fin.ext
    have := congrArg Fin.val equal
    change 3 * q + a.val = 3 * q + b.val at this
    omega

theorem fresh_ne_old (q : ℕ) (e : Fin 3) (u : Fin (3 * q)) : freshElement q e ≠ oldElement q u := by
  intro equal
  have valueEq := congrArg Fin.val equal
  have := u.isLt
  change 3 * q + e.val = u.val at valueEq
  omega

def freshTriple (q : ℕ) : Finset (Fin (3 * (q + 1))) := Finset.univ.image (freshElement q)

def Instance.paddedTriples {q m : ℕ} (I : Instance q m) : Fin (m + 1) → Finset (Fin (3 * (q + 1))) :=
  Fin.cases (freshTriple q) (fun j => (I.triples j).image (oldElement q))

@[simp] theorem old_mem_padded {q m : ℕ} (I : Instance q m) (e : Fin (3 * q)) (j : Fin m) :
    oldElement q e ∈ I.paddedTriples j.succ ↔ e ∈ I.triples j := by
  simp [Instance.paddedTriples, (oldElement q).injective.eq_iff]

@[simp] theorem old_not_fresh (q : ℕ) (e : Fin (3 * q)) : oldElement q e ∉ freshTriple q := by
  simp only [freshTriple, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun u => fresh_ne_old q u e

@[simp] theorem fresh_not_old {q m : ℕ} (I : Instance q m) (e : Fin 3) (j : Fin m) :
    freshElement q e ∉ I.paddedTriples j.succ := by
  simp only [Instance.paddedTriples, Fin.cases_succ, Finset.mem_image, not_exists, not_and]
  exact fun u _ => (fresh_ne_old q e u).symm

@[simp] theorem fresh_mem_fresh (q : ℕ) (e : Fin 3) : freshElement q e ∈ freshTriple q :=
  Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩

def Instance.pad {q m : ℕ} (I : Instance q m) : Instance (q + 1) (m + 1) where
  triples := I.paddedTriples
  triple_card := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Instance.paddedTriples, Fin.cases_zero, freshTriple,
        Finset.card_image_of_injective _ (freshElement q).injective, Finset.card_univ, Fintype.card_fin]
    · simpa only [Instance.paddedTriples, Fin.cases_succ,
        Finset.card_image_of_injective _ (oldElement q).injective] using I.triple_card i
  distinct := by
    intro i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases (fun _ => rfl) (fun b same => ?_) j
      have fresh : freshElement q 0 ∈ I.paddedTriples 0 := fresh_mem_fresh q 0
      have missing := fresh_not_old I (0 : Fin 3) b
      exact False.elim (missing (same ▸ fresh))
    · intro j
      refine Fin.cases ?_ (fun b same => ?_) j
      · intro same
        have fresh : freshElement q 0 ∈ I.paddedTriples 0 := fresh_mem_fresh q 0
        have missing := fresh_not_old I (0 : Fin 3) a
        exact False.elim (missing (same.symm ▸ fresh))
      · apply congrArg Fin.succ
        apply I.distinct
        exact (Finset.image_injective (oldElement q).injective) same

def padChosen {m : ℕ} (chosen : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  insert 0 (chosen.image Fin.succ)

def unpadChosen {m : ℕ} (chosen : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun j => j.succ ∈ chosen)

theorem Instance.padded_old_filter {q m : ℕ} (I : Instance q m)
    (chosen : Finset (Fin (m + 1))) (e : Fin (3 * q)) :
    chosen.filter (fun j => oldElement q e ∈ I.pad.triples j) =
      ((unpadChosen chosen).filter (fun j => e ∈ I.triples j)).image Fin.succ := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Instance.pad, Instance.paddedTriples]
  · simp [Instance.pad, unpadChosen]

theorem Instance.pad_cover {q m : ℕ} (I : Instance q m) (chosen : Finset (Fin m))
    (cover : I.IsExactCover chosen) : I.pad.IsExactCover (padChosen chosen) := by
  intro e
  by_cases old : e.val < 3 * q
  · let u : Fin (3 * q) := ⟨e.val, old⟩
    have eq : oldElement q u = e := Fin.ext rfl
    rw [← eq, I.padded_old_filter, Finset.card_image_of_injective _ (Fin.succ_injective m)]
    have chosenEq : unpadChosen (padChosen chosen) = chosen := by ext j; simp [unpadChosen, padChosen]
    rw [chosenEq]
    exact cover u
  · let u : Fin 3 := ⟨e.val - 3 * q, by have := e.isLt; omega⟩
    have eq : freshElement q u = e := by apply Fin.ext; change 3 * q + (e.val - 3 * q) = e.val; omega
    rw [← eq]
    have only : (padChosen chosen).filter (fun j => freshElement q u ∈ I.pad.triples j) = {0} := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [padChosen, Instance.pad, Instance.paddedTriples]
      · simp [Instance.pad]
    rw [only]
    exact Finset.card_singleton _

theorem Instance.unpad_cover {q m : ℕ} (I : Instance q m)
    (chosen : Finset (Fin (m + 1))) (cover : I.pad.IsExactCover chosen) :
    I.IsExactCover (unpadChosen chosen) := by
  intro e
  have h := cover (oldElement q e)
  rw [I.padded_old_filter, Finset.card_image_of_injective _ (Fin.succ_injective m)] at h
  exact h

theorem Instance.pad_exactCover_iff {q m : ℕ} (I : Instance q m) :
    (∃ chosen, I.pad.IsExactCover chosen) ↔ ∃ chosen, I.IsExactCover chosen := by
  exact ⟨fun ⟨chosen, cover⟩ => ⟨unpadChosen chosen, I.unpad_cover chosen cover⟩,
    fun ⟨chosen, cover⟩ => ⟨padChosen chosen, I.pad_cover chosen cover⟩⟩

/-- Adding two fresh forced triples enforces q≥2 for every input while
preserving exact-cover existence and increasing both parameters by two. -/
theorem Instance.pad_twice_exactCover_iff {q m : ℕ} (I : Instance q m) :
    (∃ chosen, I.pad.pad.IsExactCover chosen) ↔ ∃ chosen, I.IsExactCover chosen :=
  I.pad.pad_exactCover_iff.trans I.pad_exactCover_iff

end Counting.X3C
