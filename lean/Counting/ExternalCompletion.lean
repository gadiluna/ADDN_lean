import Counting.ExternalSAT

namespace Counting.External

/-- An injection of clause choices can be completed with exactly the
remaining number of slots. This is an existential matching construction,
not a search subroutine of the reduction. -/
theorem exists_completion_equiv {V : Type*} [Fintype V] [DecidableEq V]
    {m K : ℕ} (f : Fin m → V) (injective : Function.Injective f) (card : Fintype.card V = K) :
    ∃ e : Fin m ⊕ Fin (K - m) ≃ V, ∀ i, e (.inl i) = f i := by
  classical
  let remaining : Finset V := Finset.univ \ Finset.univ.image f
  have remainingCard : Fintype.card {v // v ∈ remaining} = K - m := by
    rw [Fintype.card_coe]
    unfold remaining
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ injective, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, card]
  let rest : Fin (K - m) ≃ {v // v ∈ remaining} := (Fintype.equivFinOfCardEq remainingCard).symm
  let extend : Fin m ⊕ Fin (K - m) → V := Sum.elim f (fun j => (rest j).val)
  have inj : Function.Injective extend := by
    intro a b same
    cases a with
    | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (injective same)
        | inr j =>
            have absent := (Finset.mem_sdiff.mp (rest j).property).2
            exact False.elim (absent (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, same⟩))
    | inr i =>
        cases b with
        | inl j =>
            have absent := (Finset.mem_sdiff.mp (rest i).property).2
            exact False.elim (absent (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, same.symm⟩))
        | inr j => exact congrArg Sum.inr (rest.injective (Subtype.ext same))
  have surj : Function.Surjective extend := by
    intro v
    by_cases used : v ∈ Finset.univ.image f
    · obtain ⟨i, _, equal⟩ := Finset.mem_image.mp used
      exact ⟨.inl i, equal⟩
    · have member : v ∈ remaining := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, used⟩
      refine ⟨.inr (rest.symm ⟨v, member⟩), ?_⟩
      change (rest (rest.symm ⟨v, member⟩)).val = v
      rw [rest.apply_symm_apply]
  exact ⟨Equiv.ofBijective extend ⟨inj, surj⟩, fun _ => rfl⟩

end Counting.External
